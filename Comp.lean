

def Val := Int

def Stack := List Int

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

def iexec : Instr → Config → Config :=
match 
| (LOADI n) (i, s, stk) => (i + 1, s, n :: stk)
| (LOAD v) (i, s, stk) => (i + 1, s, s v :: stk)
| ADD (i, s, stk) => (i + 1, s, (stk.tail.head + stk.head) :: stk.tail.tail)
| SUB (i, s, stk) => (i + 1, s, (stk.tail.head - stk.head) :: stk.tail.tail)
| MUL (i, s, stk) => (i + 1, s, (stk.tail.head * stk.head) :: stk.tail.tail)
| DIV (i, s, stk) => (i + 1, s, (stk.tail.head / stk.head) :: stk.tail.tail)
| (STORE v) (i, s, stk) => (i + 1, s{v ↦ (stk.head)}, stk.tail)
| (JMP n) (i, s, stk) => (i + 1 + n, s, stk)
| (JMPLESS n) (i, s, stk) =>
  if (stk.tail.head) < (stk.head)
  then (i + 1 + n, s, stk.tail.tail)
  else (i + 1, s, stk.tail.tail)
| (JMPGE n) (i, s, stk) => 
  if (stk.tail.head) ≥ (stk.head)
  then (i + 1 + n, s, stk.tail.tail)
  else (i + 1, s, stk.tail.tail)
| NOP (i, s, stk) => (i, s, stk)

-- /- redefinition for ints rather than nat -/ 
-- def nth : (l : List Instr) (n : Int) :=
-- match l with
--   | (a :: l) n => if (n = 0) 
--     then a
--     else nth l (n - 1)
--   | list.nil n => NOP

-- def nth (as : List Instr) :
-- Fin (List.length as) → Instr :=
-- match as with
--   | (a :: tail) {val := 0, isLt := isLt} = a
--   | (head :: as) { val := Nat.succ i, isLt := h } =
--     nth as { val := i, isLt := (_ : Nat.succ i ≤ List.length as) }

-- def nth (l : List Instr) (i : Int) : Instr :=
--   nth l i = if h : Instr then l[i] else NOP