# Mock final exams: COMP6260 Foundations of Computing (Dafny)

Three full mock papers, each **50 marks**, in the same format as the 2026 mid-term:
one `.dfy` file per question, where you replace `/* YOUR WORK GOES HERE */`.

| Folder | Q1 (7) | Q2 (8) | Q3 (8) | Q4 (9) | Q5 (10) | Q6 (8, COMP6260) |
|---|---|---|---|---|---|---|
| `version-A` | records, predicates, preconditions | list `count`, induction, aux lemma | trees, `{:induction false}` | loops, invariants, 3 complaints, `decreases` | seqs, arrays, `old`, untouched part | `exists` witnesses, partition loop |
| `version-B` | termination, lexicographic, mutual recursion | lists as sets, `subset` | accumulators, generalising | fib-style loops, `decreases *` | arrays: `reads`, `fresh`, frame, multiset | sorted seqs, binary search |
| `version-C` | `option`, dictionaries | BST insert, `bst` invariant | `divides`, `forall`/`exists` proofs | method specs, opacity, `break` | seq ops, `isSorted`, `findMax` | data invariant (array stack) |
| `extra-challenge.dfy` | reverse in place (3 regions), selection sort, nested-loop `nodup` | | | | | |

Each `qN.dfy` has a matching `qN-soln.dfy`. Every version folder has its own `core-list.dfy`, so the `include` lines work.

## How to use them (aim: 40/50)

1. Do one version under exam conditions with **no notes**: open `qN.dfy` in VS Code, write your answer, and keep going until Dafny shows no errors.
2. Mark it with the `-soln.dfy` files. A wrong answer often still verifies, so compare your statements line by line.
3. Redo whatever you got wrong 2 days later, then move to the next version. Finish with `extra-challenge.dfy`.

## The mistakes that cost you marks in the mid-term

- **Stating a tautology.** In Q2E/Q2F you wrote `ensures mt_lt(a,b)==true || mt_lt(a,b)==false`. That is true of *every* predicate, so it proves nothing and gets 0. Before you write `{}`, read your `ensures` back in English and check it is the property the question asked for (for example `mt_lt(a,b) || a == b || mt_lt(b,a)`).
- Write `P` instead of `P == true`, and `!P` instead of `P == false`.

## Loop invariant checklist (about 40% of the final)

1. **Counting**: `i <= n` (or `i <= a.Length`). Together with the negated guard it gives `i == n` at the end.
2. **Computing**: the postcondition with `n` replaced by `i` (`r == power(b, i)`, `forall j :: 0 <= j < i ==> ...`).
3. **Arrays you modify**: also say what is **not touched yet**: `forall j :: i <= j < a.Length ==> a[j] == old(a[j])`.
4. **Swaps**: `multiset(a[..]) == multiset(old(a[..]))`.
5. **Termination**: `decreases n - i`, `decreases hi - lo`, `decreases n`. For `while lo < hi`, use `hi - lo`.
6. Read the complaint: *not hold on entry* → the initial values are wrong. *Not maintained* → the invariant is too weak or the body is wrong. *Postcondition* → a computing invariant is missing.

Note: the solutions have not been run through Dafny, because no verifier was available here. They follow the patterns that verify in the lecture code. If one fails in your VS Code, the usual fix is one extra `assert` of the intermediate fact.
