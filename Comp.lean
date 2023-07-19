-- TODO: port star from LoVe to Lean 4
-- inductive star {α : Sort} (r : α → α → Prop) (a : α) : α → Prop where
-- | refl _    : star a
-- | tail {b c} : star b → r b c → star c

-- attribute [refl] star.refl

-- variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

-- @[trans] lemma trans (hab : star r a b) (hbc : star r b c) :
--   star r a c :=
-- begin
--   induction' hbc,
--   case refl {
--     assumption },
--   case tail : c d hbc hcd hac {
--     exact (tail (hac hab)) hcd }
-- end

-- lemma single (hab : r a b) :
--   star r a b :=
-- refl.tail hab

-- lemma head (hab : r a b) (hbc : star r b c) :
--   star r a c :=
-- begin
--   induction' hbc,
--   case refl {
--     exact (tail refl) hab },
--   case tail : c d hbc hcd hac {
--     exact (tail (hac hab)) hcd }
-- end

-- lemma head_induction_on {α : Sort*} {r : α → α → Prop} {b : α}
--   {P : ∀a : α, star r a b → Prop} {a : α} (h : star r a b)
--   (refl : P b refl)
--   (head : ∀{a c} (h' : r a c) (h : star r c b), P c h → P a (h.head h')) :
--   P a h :=
-- begin
--   induction' h,
--   case refl {
--     exact refl },
--   case tail : b c hab hbc ih {
--     apply ih,
--     show P b _, from
--       head hbc _ refl,
--     show ∀a a', r a a' → star r a' b → P a' _ → P a _, from
--       assume a a' hab hbc, head hab _ }
-- end

-- lemma trans_induction_on {α : Sort*} {r : α → α → Prop}
--     {p : ∀{a b : α}, star r a b → Prop} {a b : α} (h : star r a b)
--     (ih₁ : ∀a, @p a a refl) (ih₂ : ∀{a b} (h : r a b), p (single h))
--     (ih₃ : ∀{a b c} (h₁ : star r a b) (h₂ : star r b c), p h₁ →
--        p h₂ → p (h₁.trans h₂)) :
--   p h :=
-- begin
--   induction' h,
--   case refl {
--     exact ih₁ a },
--   case tail : b c hab hbc ih {
--     exact ih₃ hab (single hbc) (ih ih₁ @ih₂ @ih₃) (ih₂ hbc) }
-- end

-- lemma lift {β : Sort*} {s : β → β → Prop} (f : α → β)
--   (h : ∀a b, r a b → s (f a) (f b)) (hab : star r a b) :
--   star s (f a) (f b) :=
-- hab.trans_induction_on
--   (assume a, refl)
--   (assume a b, single ∘ h _ _)
--   (assume a b c _ _, trans)

-- lemma mono {p : α → α → Prop} :
--   (∀a b, r a b → p a b) → star r a b → star p a b :=
-- lift id

-- lemma star_star_eq :
--   star (star r) = star r :=
-- funext
--   (assume a,
--    funext
--      (assume b,
--       propext (iff.intro
--         (assume h,
--          begin
--            induction' h,
--            { refl },
--            { transitivity;
--                assumption }
--          end)
--         (star.mono (assume a b,
--            single)))))




def Val := Int

def Stack := List Int

def Stack.tail (stk : Stack) : Stack :=
match stk with 
| [] => []
| (_ :: t) => t


/-
  Accomodating for Isabelle's support of head []
  N.B. only problem of this could be if the stack is not controlled and the division is by zero
-/
def Stack.head (stk : Stack) : Int :=
match stk with
| [] => 0
| (a::_) => a    

def State : Type := String → Int

def State.update (name : String) (val : Int) (s : State) : State :=
fun name' => if name' == name then val else s name'


notation s "{" name " ↦ " val "}" => State.update name val s


-- @[simp] theorem update_apply (name : String) (val : Int) (s : State) : State :=
--   State.update name val s :=
-- if_pos rfl

-- @[simp] lemma update_apply_ne (name name' : vname) (val : ℤ) (s : State)
--     (h : name' ≠ name) :
--   s{name ↦ val} name' = s name' :=
-- if_neg h

-- @[simp] lemma update_override (name : vname) (val₁ val₂ : ℤ) (s : State) :
--   s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
-- begin
--   apply funext,
--   intro name',
--   by_cases name' = name;
--     simp [h]
-- end

-- @[simp] lemma update_swap (name₁ name₂ : vname) (val₁ val₂ : ℤ) (s : State)
--     (h : name₁ ≠ name₂) :
--   s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
-- begin
--   apply funext,
--   intro name',
--   by_cases name' = name₁;
--     by_cases name' = name₂;
--     simp * at *
-- end

-- @[simp] lemma update_id (name : vname) (s : State) :
--   s{name ↦ s name} = s :=
-- begin
--   apply funext,
--   intro name',
--   by_cases name' = name;
--     simp * at *
-- end

-- @[simp] lemma update_same_const (name : vname) (val : ℤ) :
--   (λ_, val){name ↦ val} = (λ_, val) :=
-- by apply funext; simp


def Config := Int × State × Stack

inductive Instr : Type where
| LOADI : Int → Instr
| LOAD : String → Instr 
| ADD : Instr
| SUB : Instr
| MUL : Instr
| DIV : Instr
| STORE : String → Instr
| JMP : Int → Instr
| JMPLESS : Int → Instr
| JMPGE : Int → Instr
| NOP : Instr

open Instr

def iexec (a : Instr) (c : Config) : Config :=
match a with
| (LOADI n) => (c.fst + 1, c.snd.fst, n :: c.snd.snd)
| (LOAD v) => (c.fst + 1, c.snd.fst, c.snd.fst v :: c.snd.snd)
| ADD => (c.fst + 1, c.snd.fst, (c.snd.snd.tail.head + c.snd.snd.head) :: c.snd.snd.tail.tail)
| SUB => (c.fst + 1, c.snd.fst, (c.snd.snd.tail.head - c.snd.snd.head) :: c.snd.snd.tail.tail)
| MUL => (c.fst + 1, c.snd.fst, (c.snd.snd.tail.head * c.snd.snd.head) :: c.snd.snd.tail.tail)
| DIV => (c.fst + 1, c.snd.fst, (c.snd.snd.tail.head / c.snd.snd.head) :: c.snd.snd.tail.tail)
| (STORE v) => (c.fst + 1, c.snd.fst{v ↦ (c.snd.snd.head)}, c.snd.snd.tail)
| (JMP n) => (c.fst + 1 + n, c.snd.fst, c.snd.snd)
| (JMPLESS n) =>
  if (c.snd.snd.tail.head) < (c.snd.snd.head)
  then (c.fst + 1 + n, c.snd.fst, c.snd.snd.tail.tail)
  else (c.fst + 1, c.snd.fst, c.snd.snd.tail.tail)
| (JMPGE n) => 
  if (c.snd.snd.tail.head) ≥ (c.snd.snd.head)
  then (c.fst + 1 + n, c.snd.fst, c.snd.snd.tail.tail)
  else (c.fst + 1, c.snd.fst, c.snd.snd.tail.tail)
| NOP => c

def nth (l : List Instr) (n : Int) : Instr :=
  match l with
  | [] => NOP
  | (a :: l) => if (n = 0) 
      then a
      else nth l (n - 1)

/- 
  ## Single step execution
  Execute one instruction
  check if pc is in a valid location in the list 
-/
def exec1  (li : List Instr) (c : Config)  (c' : Config) : Prop := 
( c' = iexec (nth li c.fst) c ∧ 0 ≤ c.fst ∧ c.fst < li.length)  

/-
  ## Intro rule
-/
theorem exec1I (li : List Instr)
  (h_eq: c' = iexec (nth li i) (i, s, stk))
  (h_nneg : 0 ≤ i) 
  (h_less : i < li.length):
  exec1 li (i, s, stk) c' := by
    simp [exec1]
    simp [h_eq, h_nneg, h_less]
  

-- /- ## Multiple step execution -/
-- def exec (li : List Instr) (c : Config) (c' : Config) : Prop :=
-- star (exec1 li) c c'

theorem iexec_shift_without_jmp {n : Int}  {i' : Int} {i : Int}:
n + i' = n + i + 1 ↔ i' = i + 1 :=
by
  apply Iff.intro
  . intro h_no_brackets
    simp at h_no_brackets
    sorry
  . intro h
    simp [h]
    -- simp [Int.add_assoc]
    sorry
--   {
--     intro h_no_brackets,
--     have h_brackets: n + i' = n + (i + 1) := 
--     begin
--       simp [h_no_brackets],
--       cc,
--     end,
--     apply int.add_left_cancel,
--     apply h_brackets,
--   },
--   {
--     intro h3,
--     simp [h3],
--     cc,
--   },
-- end

theorem iexec_shift :
((n + i',s',stk') = iexec instr (n + i, s, stk)) = ((i',s',stk') = iexec instr (i,s,stk)) := by
cases instr
case LOADI =>
  simp [iexec]
  sorry
case LOAD =>
  simp [iexec]
  sorry
case ADD =>
  simp [iexec]
  sorry
case SUB =>
  simp [iexec]
  sorry
case MUL =>
  simp [iexec]
  sorry
case DIV =>
  simp [iexec]
  sorry
case STORE =>
  simp [iexec]
  sorry
case JMP => sorry
case JMPLESS => sorry
case JMPGE => sorry
case NOP => 
  simp [iexec]
  sorry
  -- apply iexec_shift_without_jmp
  
-- match instr with
-- | (LOADI n) => 