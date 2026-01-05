# ADR-0002: Reconsideration of the B-Tree type decision

- **Status:** Accepted
- **Date:** 2026-01-05

## Context

In the very last ADR we decided to implement a simpler B-Tree type where nodes are not ballanced. Following this
decision, I continued my reflexion on this data structure and realized the tradeoffs involved in this choice are not
desirable for our use case.

## Options Considered

### Option A: Follow ADR-0001

- Key tradeoffs:
    - Cons:
        - Nodes can become unbalanced
        - Does not follow the architecture of project we are inspired-by

### Option B: Reverse the ADR-0001 decision and implement a balanced B-Tree
We implement a balanced B-Tree as initially planned.

## Decision

Option B is chosen.

## Rationale

The tradeoffs of ADR-0001 were not desirable.

## References

[ADR-0001: B-Tree type](./0001-b-tree-type.md)