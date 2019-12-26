# Notes on refinement:

In the latest approach, we no longer have a dedicated special recovery procedure
that always runs immediately after crashing.  Rather, a layer may just provide a
"recovery" operation. On restart we run some fixed program (a dispatch handler,
say), which can always choose to call this recovery operation. We can set up the
transition relation for the layer's operations to make it so that calls to any
other operation after a crash trigger undefined behavior. Thus, if necessary, we can still
*encode* a pattern in which recovery has to be called upon start up, but we have
the flexibility to consider other deferred recovery patterns.

However, if recovery is no longer a dedicated special procedure, but just an
operation that might be called at a certain point, then the simulation proof has
an extra layer of complexity. Let's say we crashed executing program e, and
after restart begin executing e'. We may need to start simulating new steps of
e' *before* we do any helping to complete pending operations of e.

That is because, even if the semantics of the extension we're refining makes it
UB to to perform other external operations before calling "recovery", the base
Goose lang semantics would still allow doing in-memory heap operations before
recovery.


## Example: Lazy Replicated Disk

Consider the following variant of the replicated disk example, which captures
some of the challenges, just as the original replicated disk did for helping in
Perennial 1.  On restart, recovery does not propagate any writes at
all. Instead, it just re-allocates locks for all the blocks. Besides these
locks, it creates an in-memory bitmap, with a bit for every block, and sets
these bits all to 1. The idea is that entry i is 1 if block i is potentially out
of sync. The lock for a block also protects its bitmap entry.

(Note: in a real system I think an on-disk bit map would be used to speed up
recovery by marking blocks that could potentially be out of sync, but that's not
the purpose here.)

Writes behave as before, except that they additionally clear the dirty bit after
they finish their write to the back-up disk.

Reads read the primary disk and then check the dirty bit. If it is 1, they
propagate the write to the back-up disk and then clear the bit before releasing
the lock. (If either disk has failed then of course there's no write to
propagate and they can also just clear the bit.)

### Why is this correct?

This is sound because even if the disks are out of sync at some block
post-crash, this is not visible until we try to read there. When we do the read,
if they are in fact out of sync, then the read will put them back in sync. This
propagating write is justified because there must have been some crashed write
which is now being helped.

However: the big twist here relative to Perennial 1 is that this crashed write
may have been from several crashes ago, and meanwhile we have been potentially
simulating steps for other operations to the disk! At any given time several
different "generations" of crashed writes could be helped by different threads,
so we may be inserting extra steps at many different points in the simulated
execution.

But if the framework is set up correctly, ideally the user of the framework
should do basically the same proof as before for the normal replicated disk.

We need to argue that all of the other operations in the simulated execution
that go after the write we're about to help would be unaffected. But somehow,
that should follow from the usual separation logic principle that they are
operating on a disjoint part of the disk.
