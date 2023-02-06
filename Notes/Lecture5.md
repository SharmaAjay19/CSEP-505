## How to define states in a program

(valuation, cmd) i.e. a state of memory and a program counter of the next instruction to be executed.

## How to convert states in a program (Step function)

- Assign

    (v, x := e) -> (v', Skip) i.e. no instruction after cmd.

    x := e is assignment command.

    v' can be represented as, v' = (x, e) :: v

- Seq: For a sequence of instructions

    (v, c1;c2) -> (v', c1';c2)

    (v, Skip;c2) -> (v, c2)

- If-else

    (v, if e c1 c2)
    - if e != 0 then -> (v, c1)
    - if e == 0 then -> (v, c2)

- While

    (v, while e c) -> (v, c; while e c) until e != 0

    when e == 0, (v, while e c) -> (v, Skip)

**Only Assign directly modifies the valuation.**

**Skip is proof of program termination. Skip can never step.**

SeqL starts a sequence, SeqR eliminates a sequence.

Operational semantics is a way to convert program syntax into transition system.


The program structure increases with loops and thus the proof structure. What is done to improve that situation?

Loop invariants -> What is true about the memory at every step?

magic_select_case - explain it - figures out which of the 11 disjuctions is needed.

eauto with a number is basically saying try harder. eauto 5, eauto 20.

auto is a loop around apply. eauto is a loop around eapply.

**Big Step Operational Semantics**

Compiler Optimizer

C --> Optimizer --> C0

Compiler bugs become bug in any application they compile.

For the Optimizer to be correct C and C0 should be equivalent i.e. should have the same behavior.

What does it take for them to be equivalent?

For any state (v, c) that you start and can reach (v', c') in the original program should mean that (v, opt(c)) can also reach (v', opt(c')).