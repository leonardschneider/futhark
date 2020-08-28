// start of scheduler.h
#ifndef _SCHEDULER_H_
#define _SCHEDULER_H_

#ifdef MCJOBQUEUE

static volatile int active_work = 0;

static inline int is_finished(struct worker *worker) {
  return __atomic_load_n(&worker->dead, __ATOMIC_RELAXED) && subtask_queue_is_empty(&worker->q);
}

// Try to steal from a random queue
static inline int steal_from_random_worker(struct worker* worker)
{
  int my_id = worker->tid;
  struct scheduler* scheduler = worker->scheduler;
  int k = random_other_worker(scheduler, my_id);
  struct worker *worker_k = &scheduler->workers[k];
  struct subtask* subtask =  NULL;
  int retval = subtask_queue_steal(worker_k, &subtask);
  if (retval == 0) {
    subtask_queue_enqueue(worker, subtask);
    return 1;
  }
  return 0;
}

/* Only one error can be returned at the time now
   Maybe we can provide a stack like structure for pushing errors onto
   if we wish to backpropagte multiple errors */
static inline void *scheduler_worker(void* arg)
{
  struct worker *worker = (struct worker*) arg;
  worker_local = worker;
  struct subtask * subtask = NULL;
  while(!is_finished(worker)) {
    if (!subtask_queue_is_empty(&worker->q)) {
      int retval = subtask_queue_dequeue(worker, &subtask, 0);
      if (retval == 0) {
        assert(subtask != NULL);
        struct subtask* subtask_new = chunk_subtask(worker, subtask);
        CHECK_ERR(run_subtask(worker, subtask_new), "run_subtask");
      } // else someone stole our work

    } else if (active_work) {
      /* steal */
      while (!is_finished(worker) && __atomic_load_n(&active_work, __ATOMIC_RELAXED)) {
        if (steal_from_random_worker(worker))
          break;
      }
    } else {
      // go back to sleep
      int retval = subtask_queue_dequeue(worker, &subtask, 1);
      if (retval == 0) {
        assert(subtask != NULL);
        struct subtask* subtask_new = chunk_subtask(worker, subtask);
        CHECK_ERR(run_subtask(worker, subtask_new), "run_subtask");
      }
    }
  }

  assert(subtask_queue_is_empty(&worker->q));
  __atomic_fetch_sub(&num_workers, 1, __ATOMIC_RELAXED);
  if (worker->output_usage)
    output_thread_usage(worker);
  return NULL;
}



static inline int scheduler_execute_parallel(struct scheduler *scheduler,
                                             struct scheduler_parloop *task,
                                             int64_t *timer)
{

  struct worker * worker = worker_local;

  struct scheduler_info info = task->info;
  int64_t iter_pr_subtask = info.iter_pr_subtask;
  int64_t remainder = info.remainder;
  int nsubtasks = info.nsubtasks;
  volatile int shared_counter = nsubtasks;

  // Shared timer used to sum up all
  // sequential work from each subtask
  int64_t task_timer = 0;
  int64_t task_iter = 0;

  enum scheduling sched = info.sched;
  /* Each subtasks can be processed in chunks */
  int chunkable = sched == STATIC ? 0 : 1;
  int64_t iter = 1;

  if (sched == DYNAMIC)
    __atomic_add_fetch(&active_work, 1, __ATOMIC_RELAXED);

  int subtask_id = 0;
  int64_t start = 0;
  int64_t end = iter_pr_subtask + (int)(remainder != 0);
  for (subtask_id = 0; subtask_id < nsubtasks; subtask_id++) {
    struct subtask *subtask = setup_subtask(task->fn, task->args, task->name,
                                            &shared_counter,
                                            &task_timer, &task_iter,
                                            start, end,
                                            chunkable, iter,
                                            subtask_id);
    assert(subtask != NULL);
    CHECK_ERR(subtask_queue_enqueue(&scheduler->workers[subtask_id%scheduler->num_threads], subtask),
              "subtask_queue_enqueue");
    // Update range params
    start = end;
    end += iter_pr_subtask + ((subtask_id + 1) < remainder);
  }

  // Join (wait for subtasks to finish)
  while(shared_counter != 0 && scheduler_error == 0) {
    if (!subtask_queue_is_empty(&worker->q)) {
      struct subtask *subtask = NULL;
      int err = subtask_queue_dequeue(worker, &subtask, 0);
      if (err == 0 ) {
        struct subtask* subtask_new = chunk_subtask(worker, subtask);
        CHECK_ERR(run_subtask(worker, subtask_new), "run_subtask");
      }
    } else {
      while (shared_counter != 0 && subtask_queue_is_empty(&worker->q) && scheduler_error == 0) {
        if (steal_from_random_worker(worker)) {
          struct subtask *subtask = NULL;
          int err = subtask_queue_dequeue(worker, &subtask, 0);
          if (err == 0 ) {
            struct subtask* subtask_new = chunk_subtask(worker, subtask);
            CHECK_ERR(run_subtask(worker, subtask_new), "run_subtask");
          }
        }
      }
    }
  }

  if (sched == DYNAMIC)
    __atomic_sub_fetch(&active_work, 1, __ATOMIC_RELAXED);

  // Write back timing results
  (*timer) += task_timer;
  return scheduler_error;
}

#elif defined(MCCHASELEV)

static inline int is_finished(struct worker *worker) {
  return __atomic_load_n(&worker->dead, __ATOMIC_RELAXED) && empty(&worker->q);
}

// Try to steal from a random queue
static inline int steal_from_random_worker(struct worker* worker)
{
  int my_id = worker->tid;
  struct scheduler* scheduler = worker->scheduler;
  int k = random_other_worker(scheduler, my_id);
  struct deque *deque_k = &scheduler->workers[k].q;
  if (empty(deque_k)) return 0;
  struct subtask* subtask = steal(deque_k);
  // otherwise try to steal from
  if (subtask == STEAL_RES_EMPTY) {
    // TODO: log
  } else if (subtask == STEAL_RES_ABORT) {
    // TODO: log
  } else {
    assert(subtask != NULL);
    push_back(&worker->q, subtask);
    return 1;
  }
  return 0;
}

static inline void *scheduler_worker(void* arg)
{
  struct worker *worker = (struct worker*) arg;
  worker_local = worker;
  while (!is_finished(worker))
  {
    if (!empty(&worker->q)) {
      struct subtask* subtask = pop_back(&worker->q);
      if (subtask == NULL) continue;
      struct subtask* subtask_new = chunk_subtask(worker, subtask);
      CHECK_ERR(run_subtask(worker, subtask_new), "run_subtask");
      /* Only one error can be returned at the time now
         Maybe we can provide a stack like structure for pushing errors onto
         if we wish to backpropagte multiple errors */
    } else if (__atomic_load_n(&num_workers, __ATOMIC_RELAXED) == 1) {
      break;
    } else { // try to steal
      assert(num_workers >= 2);
      while(!is_finished(worker)) {
        if (steal_from_random_worker(worker))
          break;
      }
    }
  }
  assert(empty(&worker->q));
  __atomic_fetch_sub(&num_workers, 1, __ATOMIC_RELAXED);
  if (worker->output_usage)
    output_thread_usage(worker);
  return NULL;
}


static inline int scheduler_execute_parallel(struct scheduler *scheduler,
                                             struct scheduler_parloop *task,
                                             int64_t *timer)
{
  struct worker * worker = worker_local;

  struct scheduler_info info = task->info;
  int64_t iter_pr_subtask = info.iter_pr_subtask;
  int64_t remainder = info.remainder;
  int nsubtasks = info.nsubtasks;
  enum scheduling sched = info.sched;

  volatile int shared_counter = nsubtasks;

  // Shared timer used to sum up all
  // sequential work from each subtask
  int64_t task_timer = 0;
  int64_t task_iter = 0;


  /* Each subtasks can be processed in chunks */
  int chunkable = sched == STATIC ? 0 : 1;
  int64_t iter = 1;


  int subtask_id = 0;
  int64_t start = 0;
  int64_t end = iter_pr_subtask + (int)(remainder != 0);
  for (subtask_id = 0; subtask_id < nsubtasks; subtask_id++) {
    struct subtask *subtask = setup_subtask(task->fn, task->args, task->name,
                                            &shared_counter,
                                            &task_timer, &task_iter,
                                            start, end,
                                            chunkable, iter,
                                            subtask_id);
    assert(subtask != NULL);
    push_back(&worker->q, subtask);

    // Update range params
    start = end;
    end += iter_pr_subtask + ((subtask_id + 1) < remainder);
  }

  while(shared_counter != 0 && scheduler_error == 0) {
    if (!empty(&worker->q)) {
      struct subtask * subtask = pop_back(&worker->q);
      if (subtask == NULL) continue;
      struct subtask* subtask_new = chunk_subtask(worker, subtask);
      CHECK_ERR(run_subtask(worker, subtask_new), "run_subtask");
    } else {
      while (shared_counter != 0 && empty(&worker->q) && scheduler_error == 0) {
        steal_from_random_worker(worker);
      }
    }
  }
  // Write back timing results
  (*timer) += task_timer;

  return scheduler_error;
}

#endif


static inline int scheduler_execute_task(struct scheduler *scheduler,
                                         struct scheduler_parloop *task)
{

  struct worker *worker = worker_local;

  int err = 0;
  if (task->iterations == 0) {
    return err;
  }

  int64_t task_timer = 0;
  /* Execute task sequential or parallel based on decision made earlier */
  if (task->info.nsubtasks == 1) {
    /* int64_t start = get_wall_time_ns(); */
    err = task->fn(task->args, 0, task->iterations, 0, worker->tid);
    /* int64_t end = get_wall_time_ns(); */
    /* task_timer = end - start; */
    /* worker_local->time_spent_working += task_timer; */
    // Report time measurements
    // TODO the update of both of these should really both be atomic!!
    /* __atomic_fetch_add(task->info.total_time, task_timer, __ATOMIC_RELAXED); */
    /* __atomic_fetch_add(task->info.total_iter, task->iterations, __ATOMIC_RELAXED); */
  }
  else
  {
    // Add "before" time if we already are inside a task
    int64_t time_before = 0;
    if (worker->nested > 0) {
      time_before = total_now(worker->total, worker->timer);
    }

    err = scheduler_execute_parallel(scheduler, task, &task_timer);

    // Report time measurements
    // TODO the update of both of these should really both be atomic!!
    __atomic_fetch_add(task->info.total_time, task_timer, __ATOMIC_RELAXED);
    __atomic_fetch_add(task->info.total_iter, task->iterations, __ATOMIC_RELAXED);

    // Reset timers to account for new timings
    worker->total = time_before + task_timer;
    worker->timer = get_wall_time_ns();
  }


  return err;
}

/* Decide on how schedule the incoming task i.e. how many subtasks and
   to run sequential or (potentially nested) parallel code body */
static inline int scheduler_prepare_task(struct scheduler* scheduler,
                                         struct scheduler_task *task)
{
  assert(task != NULL);

  struct scheduler_info info;
  info.total_time = task->total_time;
  info.total_iter = task->total_iter;

  int max_num_tasks = task->sched == STATIC ?
    compute_max_num_subtasks(scheduler->num_threads, info, task->iterations):
    scheduler->num_threads;

  // Decide if task should be scheduled sequentially
  if (max_num_tasks <= 1 || is_small(task, max_num_tasks)) {
    info.iter_pr_subtask = task->iterations;
    info.remainder = 0;
    info.nsubtasks = 1;
  } else {
    info.iter_pr_subtask = task->iterations / max_num_tasks;
    info.remainder = task->iterations % max_num_tasks;
    info.sched = task->sched;
    switch (task->sched) {
    case STATIC:
      info.nsubtasks = info.iter_pr_subtask == 0 ? info.remainder : ((task->iterations - info.remainder) / info.iter_pr_subtask);
      break;
    case DYNAMIC:
      // As any thread can take any subtasks, we are being safe with returning
      // an upper bound on the number of tasks such that the task allocate enough memory
      info.nsubtasks = info.iter_pr_subtask == 0 ? info.remainder : max_num_tasks;
      break;
    default:
      assert(!"Got unknown scheduling");
    }

  }
  return task->seq_fn(task->args, task->iterations, worker_local->tid, info);
}

#endif
// End of scheduler.h
