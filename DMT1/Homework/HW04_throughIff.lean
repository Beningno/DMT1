/- @@@
To prepare for this homework (1) be sure you
have read and understood the class materials
through 05_or.lean, corresponding to the "Or"
section in the online notes. (2) Refer to the
inference rules cheat sheet linked at the bottom
of the web site.
@@@ -/


/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/


-- ANSWER
theorem andImpEquiv {X Y : Prop} (h : X ∧ Y) : X ↔ Y :=
⟨λ _ => (h : X ∧ Y).right, λ _ => (h : X ∧ Y).left⟩

/- @@@
#2: Give the proof for #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- PARTIAL ANSWER, YOU COMPLETE IT

Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in this
context,  and we will then show that, in that
context, the conclusion must be true as well. So
assume P ∧ Q is true. The conclusion to be proved
is an equivalence. To prove an equivalence we need
to prove both ...

ANSWER
To prove P ∧ Q → (P ↔ Q), assume P ∧ Q. From P ∧ Q we get proves of P and Q
Then P → Q we use the hp prove of P and can do it the other way too therefore P ↔ Q.

@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a propostion
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Use this example to help you see that once you've
proved a theorem (as in #1 above) you can use it by
applying it to prove any special case, here with X
and Y in place of the formal parameters in the
statement of the theorem itself.
@@@ -/

-- Answer
axiom X : Prop
axiom Y : Prop
axiom h : X ∧ Y

#check andImpEquiv h



/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossibile. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* contruct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

-- ANSWER
theorem exFalsoK {K : Prop} : False → K
| f => False.elim f

/- @@@
Why is it safe to accept tihs definition? What do we
know that's special about *exFalsoK* that makes it ok?

ANSWER:
It's safe because False has no proofs.
That means the function exFalsoK is never applied to a real argument basiclly
saying if the impossible were true, then anything at all would follow.


@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are aribtrary propositions, then False *and*
P implies Q.
@@@-/

-- ANSWER
theorem false_and_imp' {P Q : Prop} (h : False ∧ P) : Q :=
let ⟨f, _⟩ := h; False.elim f

/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.

ANSWER
We prove the statement “if False ∧ P then Q” for arbitrary
propositions P and Q. Assume False ∧ P. By elim
we obtain a proof f of False. From f : False we may apply the principle
False.elim (ex falso quodlibet) to produce a proof of any proposition,
in particular Q. Thus False ∧ P implies Q.
@@@ -/




/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/


-- ANSWER
theorem false_implies_false' (f : False) : False := f
--Assume a proof f of False. Then f itself is a proof of False;
--so from the assumption we immediately return the same f
