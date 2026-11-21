# Push-Optimal Sokoban Solver

[![make.fun bounty](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/verrydimah-cpu/sokoban-solver/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/verrydimah-cpu/sokoban-solver/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)

An entry for make.fun's [“Build the best Sokoban solver, 21 November 2026”](https://make.fun/bounty/sokoban-solver-01-run-20261121) bounty. One program, `main.ts` (Node 22, standard library only), reads every instance of a set from `/input/<id>/level.txt` (XSB format) and writes the player's moves to `/output/<id>/solution.txt`.

## Why push-optimal

The checker pays the full 1,000 points for a level only when the solution uses P\* pushes — the level's push optimum. One push over P\* already earns under half, and an unsolved level earns nothing. So the solver never searches in step space; every search below works in pushes.

## Approach

1. **Room decomposition.** The drawn levels are a one-square-wide hallway with rooms opening off it through single doors, and a box pushed out of its room can never be pushed back — so every box stays in its room and the level's optimum is the sum of its rooms' optima. Cutting the dead squares of the player's row splits the floor into components; each component holding boxes is a room. Rooms are solved in turn, with the other rooms' boxes (or their goals, once that room is done) standing as walls, and the player walking on from where the last room left them.
2. **A\* over pushes per room.** A state is the sorted box squares plus the lowest square of the player's reachable region, so one position is one state wherever in a region the player stands. Successors are single pushes, generated from the player's flood-filled region.
3. **Matching heuristic.** Each goal gets an exact single-box push-distance field, pulled back over open floor. The estimate for a position is the cheapest assignment of boxes to goals under those distances (subset DP up to 8 boxes, nearest-goal sums beyond). One push moves one box one square, so the estimate is admissible and consistent — the first goal state the A\* settles is push-optimal.
4. **Deadlock pruning.** A box landing on a dead square (a square from which no push sequence reaches any goal) or completing a frozen 2×2 block of walls and boxes with a box off its goal ends that line of search immediately.
5. **Fallbacks.** A level that does not split into rooms gets one whole-level A\* under the same rules. If a search ever exhausts its work budget, the instance is answered with an empty (valid) solution rather than a wrong one. Every answer is replayed in-process before it is written, so an illegal or unsolved move string is never emitted.

## Determinism

Budgets are counted in expanded states, never read from the clock; direction order and heap tie-breaks are fixed. Two runs on the same set write byte-identical answers.

## Local check

Against the kit's practice set the solver scores the maximum: all five instances solved in exactly P\* pushes (13, 16, 29, 47, 60), in well under a second for the whole set — the house baseline (a move-based A\*) solves only the first practice level. The same result holds on fresh sets drawn with the kit's own generator from other seeds.

## License

MIT — see [LICENSE](LICENSE).
