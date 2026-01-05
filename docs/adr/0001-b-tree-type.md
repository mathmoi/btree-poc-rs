# ADR-0001: B-Tree type

- **Status:** Superseded by [ADR-0002: Reconsideration of the B-Tree type decision](./0002-reconsideration-b-tree-type-decision.md)
- **Date:** 2025-12-23

## Context

Writing the proof of concept for an inplementation of a B-Tree data structure based on what is done by SQLite, it
apprears that the implementation of a B*-Tree where the balancing algorithm borrows items from sibling nodes instead
of always splitting is really complex and should be avoided for now to keep the implementation simple.

## Options Considered

### Option A: Implementing a B*-Tree
Implement a B*-Tree where nodes can borrow items from sibling nodes like SQlite does.

Key tradeoffs:
- Pros:
    - Better solution
    - Interesing challenge
- Cons:
    - More complex to implement
    - Does not respect the MVP principle for a proof of concept

### Option B: Implementing a simpler B+Tree
Implement a simpler B+Tree where nodes are always split when they reach maximum capacity and where we allow nodes to 
underflow.

Key tradeoffs:
- Pros:
    - Simpler to implement
    - Respects the MVP principle for a proof of concept
    - We can always improve it later on
- Cons:
    - Not as good as a B*-Tree
    - undeflown nodes are not aptimal and might need to have a VACUMM operation later on

## Decision

I have decided to go with Option B: Implementing a simpler B+Tree.

## Rationale

The simpler solution will allow me to move on with other parts of the project and is technically correct even if not 
optimal. We can always improve the implementation later on if needed.

## References

- [Conversation with Claude about this decision](https://claude.ai/share/1aa081a9-df52-49ab-9bf4-d25da91f8250)