# Task board

This directory is a simple task board. **One markdown file = one task.** Add,
claim, and finish tasks just by creating and editing these `.md` files with your
normal file tools — no server, no JSON. The web UI reads these same files to draw
the board, so anything you write here shows up there.

## File format

    ---
    title: short title of the task
    status: todo            # todo | in_progress | done
    claimed_by:            # your sibling id, or a name (optional)
    created: <iso8601>
    updated: <iso8601>
    ---

    ## Description
    what the task is / what "done" looks like

    ## Progress
    - (timestamp) a running log of what you tried / found

    ## Writeup
    (fill this in when done: findings, how the code works, and any assumptions
     you made — this is what the human reads to understand what happened)

## Workflow

- **Pick a task:** open a `status: todo` file, set `status: in_progress`, and put
  your id in `claimed_by`. Prefer a task nobody else has claimed.
- **Make a new task:** create `board/<slug>.md` with `status: todo`. Break big
  work into small, checkable tasks.
- **Log progress:** append to `## Progress` as you go, so the next you (and the
  human) can follow the thread.
- **Finish:** set `status: done` and fill in `## Writeup` — findings, how the
  code works, assumptions. Be honest about what's partial or unverified.
- **Commit:** once a task is done, commit your work with git
  (`git add -A && git commit -m "<what you did>"`) so the finished task and its
  writeup are checkpointed.

Files starting with `.` or `_`, plus this README, are ignored by the board.
