/* MOCK FINAL EXAM 2026 (Version A): Question 1.  -- SOLUTIONS

   7 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: records (datatypes with named fields), predicates,
   functions with preconditions, testing lemmas, simple lemmas.
*/

datatype time = T(hour: nat, minute: nat)

predicate valid_time(t: time) { t.hour < 24 && t.minute < 60 }

/* 1A.
   Define the predicate earlier(t1, t2), which is true exactly
   when time t1 is strictly earlier in the day than time t2.
   (Hours are more significant than minutes.)

   1 mark
*/
predicate earlier(t1: time, t2: time)
{
  t1.hour < t2.hour || (t1.hour == t2.hour && t1.minute < t2.minute)
}

/* 1B.
   State and prove the testing lemma that 9:59 is earlier
   than 10:00.

   1 mark
*/
lemma earlier_test()
  ensures earlier(T(9, 59), T(10, 0)) {}

/* 1C.
   State and prove that earlier is transitive: if t1 is earlier
   than t2 and t2 is earlier than t3, then t1 is earlier than t3.

   2 marks
*/
lemma earlier_trans(t1: time, t2: time, t3: time)
  requires earlier(t1, t2)
  requires earlier(t2, t3)
  ensures earlier(t1, t3)
{}

/* 1D.
   Define tick(t), the time one minute after t.  23:59 ticks
   over to 0:00.  The function may only be called on valid times
   (this precondition is given).

   1 mark
*/
function tick(t: time) : time
  requires valid_time(t)
{
  if t.minute < 59 then T(t.hour, t.minute + 1)
  else if t.hour < 23 then T(t.hour + 1, 0)
  else T(0, 0)
}

/* 1E.
   State and prove that tick of a valid time is valid.

   1 mark
*/
lemma tick_valid(t: time)
  requires valid_time(t)
  ensures valid_time(tick(t))
{}

/* 1F.
   State and prove that for every valid time t other than 23:59,
   t is earlier than tick(t).

   1 mark
*/
lemma tick_later(t: time)
  requires valid_time(t)
  requires t != T(23, 59)
  ensures earlier(t, tick(t))
{}
