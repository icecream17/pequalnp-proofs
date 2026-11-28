import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

/-!
# Exact gate count for L-meta-24221

Five essential inputs and mixed polarities force one live shared wire and
one live NOT in any hypothetical six-gate realization. The shared wire is
upstream of the NOT. With both wires cut, the signed paths constrain the
inputs to each of the three Boolean expressions. Four promised rows
then contradict their polarities. The desk's seven-gate witness supplies
the matching upper bound.
-/

namespace StructuralRefutation24221

/-- Row r represents the six Boolean inputs given by the low bits of r. -/
def rows : List Nat :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48]

/-- True rows of the promised graph with mask 274910143. -/
def target (r : Nat) : Bool :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 24, 33, 34, 36].contains r

/-- Check the transcription against the unit's graph mask, including singleton rows. -/
theorem target_matches (i j : Fin 6) :
    target ((2 ^ i.val) ||| (2 ^ j.val)) =
      (274910143 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
  revert i j
  decide

/-- A promised input edge is an allowed single-input toggle. -/
abbrev promisedEdge (i : Fin 6) (low : Fin 64) : Prop :=
  low.val ∈ rows ∧ low.val.testBit i.val = false ∧
    (low.val ||| (2 ^ i.val)) ∈ rows

theorem five_essential (i : Fin 6) (hi : i ≠ 3) :
    ∃ low : Fin 64, promisedEdge i low ∧
      target low.val ≠ target (low.val ||| (2 ^ i.val)) := by
  revert i
  decide +kernel

theorem two_binates (i : Fin 6) (hi : i = 1 ∨ i = 2) :
    ∃ rising falling : Fin 64,
      promisedEdge i rising ∧ promisedEdge i falling ∧
      target rising.val = false ∧ target (rising.val ||| (2 ^ i.val)) = true ∧
      target falling.val = true ∧ target (falling.val ||| (2 ^ i.val)) = false := by
  refine ⟨32, 16, ?_⟩
  revert i
  decide +kernel

/-- A signed path, oriented from an input towards the output. Each edge
inherits the sign of the gate that consumes the wire. -/
inductive SignedPath (edge : Nat → Nat → Prop) (negates : Nat → Bool) (root : Nat) :
    Nat → Bool → Prop
  | done : SignedPath edge negates root root true
  | next {a b : Nat} {sign : Bool} (link : edge a b)
      (tail : SignedPath edge negates root b sign) :
      SignedPath edge negates root a (if negates b then !sign else sign)

theorem SignedPath.start_le {edge : Nat → Nat → Prop} {negates : Nat → Bool} {root a : Nat}
    {sign : Bool} (p : SignedPath edge negates root a sign)
    (forward : ∀ i j, edge i j → i < j) : a ≤ root := by
  induction p with
  | done => exact Nat.le_refl _
  | @next a b sign link tail ih => exact Nat.le_trans (Nat.le_of_lt (forward a b link)) ih

/-- The first divergence of two oppositely signed paths is a shared wire.
If there is just one such wire, the input must reach it. -/
theorem SignedPath.diverges_with_suffixes {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {sign other : Bool}
    (p : SignedPath edge negates root a sign) (q : SignedPath edge negates root a other)
    (forward : ∀ i j, edge i j → i < j) (different : sign ≠ other) :
    ∃ branch left right : Nat, left ≠ right ∧ edge branch left ∧ edge branch right ∧
      ∃ prefixSign first second : Bool,
        SignedPath edge negates branch a prefixSign ∧
        SignedPath edge negates root branch first ∧
        SignedPath edge negates root branch second ∧ first ≠ second := by
  induction p generalizing other with
  | done =>
    cases q with
    | done => exact (different rfl).elim
    | @next a b sign link tail =>
      have h₁ := forward _ _ link
      have h₂ := tail.start_le forward
      omega
  | @next a b sign link tail ih =>
    cases q with
    | done =>
      have h₁ := forward _ _ link
      have h₂ := tail.start_le forward
      omega
    | @next _ c other link' tail' =>
      by_cases same : b = c
      · subst c
        have differTail : sign ≠ other := by
          intro h
          exact different (congrArg (fun s => if negates b then !s else s) h)
        obtain ⟨branch, left, right, ne, e₁, e₂, _, first, second, headPath, fin₁, fin₂, neSign⟩ :=
          ih tail' differTail
        exact ⟨branch, left, right, ne, e₁, e₂, _, first, second,
          .next link headPath, fin₁, fin₂, neSign⟩
      · exact ⟨a, b, c, same, link, link', true, _, _, .done,
          .next link tail, .next link' tail', different⟩

theorem SignedPath.reaches_unique_branch {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a shared : Nat} (p : SignedPath edge negates root a true)
    (q : SignedPath edge negates root a false) (forward : ∀ i j, edge i j → i < j)
    (unique : ∀ v l r, l ≠ r → edge v l → edge v r → v = shared) :
    ∃ sign, SignedPath edge negates shared a sign := by
  obtain ⟨branch, l, r, ne, el, er, sign, _, _, initialPath, _, _, _⟩ :=
    p.diverges_with_suffixes q forward (by decide)
  exact ⟨sign, unique branch l r ne el er ▸ initialPath⟩

theorem SignedPath.snoc {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a b : Nat} {sign : Bool}
    (path : SignedPath edge negates root a sign) (link : edge root b) :
    SignedPath edge negates b a (if negates b then !sign else sign) := by
  induction path with
  | done => exact .next link .done
  | @next x y sign step tail ih =>
    have extended := SignedPath.next step ih
    cases h₁ : negates y <;> cases h₂ : negates b <;> simpa [h₁, h₂] using extended

inductive Formula
  | input (index : Nat)
  | constant (value : Bool)
  | and (left right : Formula)
  | or (left right : Formula)
  | not (arg : Formula)

def Formula.eval (x : Nat → Bool) : Formula → Bool
  | .input i => x i
  | .constant b => b
  | .and a b => a.eval x && b.eval x
  | .or a b => a.eval x || b.eval x
  | .not a => !(a.eval x)

/-- A path is positive when it passes through an even number of NOTs. -/
def Formula.hasPolarity (i : Nat) (positive : Bool) : Formula → Prop
  | .input j => j = i ∧ positive = true
  | .constant _ => False
  | .and a b | .or a b => a.hasPolarity i positive ∨ b.hasPolarity i positive
  | .not a => a.hasPolarity i (!positive)

/-- A change in the output of an unfolded circuit has a matching input path.
This lets rising and falling rows certify that both signs occur. -/
theorem Formula.polarity_of_change (f : Formula) (x y : Nat → Bool) (i : Nat)
    (agree : ∀ j, j ≠ i → x j = y j) (hi : y i = true)
    (positive : Bool) (hx : f.eval x = !positive) (hy : f.eval y = positive) :
    f.hasPolarity i positive := by
  induction f generalizing positive with
  | input j =>
    by_cases h : j = i
    · subst j
      exact ⟨rfl, hy.symm.trans hi⟩
    · have same := agree j h
      cases positive <;> simp_all [Formula.eval]
  | constant v =>
    cases positive <;> simp_all [Formula.eval]
  | and a b ihA ihB =>
    cases positive <;>
      cases exA : a.eval x <;> cases eyA : a.eval y <;>
      cases exB : b.eval x <;> cases eyB : b.eval y <;>
      simp_all [Formula.eval, Formula.hasPolarity]
  | or a b ihA ihB =>
    cases positive <;>
      cases exA : a.eval x <;> cases eyA : a.eval y <;>
      cases exB : b.eval x <;> cases eyB : b.eval y <;>
      simp_all [Formula.eval, Formula.hasPolarity]
  | not a ih =>
    apply ih (!positive)
    · cases positive <;> simpa [Formula.eval] using hx
    · cases positive <;> simpa [Formula.eval] using hy

open PEqualNP.CircuitLowerBounds

def supported (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

def Formula.read (wires : List Formula) (i : Nat) : Formula :=
  wires.getD i (.constant false)

def Formula.fromGate (wires : List Formula) (g : Gate) : Formula :=
  let args := g.inputs.map (Formula.read wires)
  match g.op with
  | .and => args.foldr Formula.and (.constant true)
  | .or => args.foldr Formula.or (.constant false)
  | .not => .not (args.getD 0 (.constant false))
  | _ => .constant false

private theorem Formula.eval_read (x : Nat → Bool) (wires : List Formula) (i : Nat) :
    (Formula.read wires i).eval x = (wires.map (Formula.eval x)).getD i false := by
  simp only [Formula.read, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases wires[i]? <;> rfl

private theorem Formula.eval_and (x : Nat → Bool) (args : List Formula) :
    (args.foldr Formula.and (.constant true)).eval x = (args.map (Formula.eval x)).all id := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [Formula.eval, ih]

private theorem Formula.eval_or (x : Nat → Bool) (args : List Formula) :
    (args.foldr Formula.or (.constant false)).eval x = (args.map (Formula.eval x)).any id := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [Formula.eval, ih]

private theorem Formula.eval_fromGate (x : Nat → Bool) (wires : List Formula) (g : Gate)
    (hg : supported g) :
    (Formula.fromGate wires g).eval x =
      g.op.eval (g.inputs.map fun i => (wires.map (Formula.eval x)).getD i false) := by
  have reads : (g.inputs.map (Formula.read wires)).map (Formula.eval x) =
      g.inputs.map (fun i => (wires.map (Formula.eval x)).getD i false) := by
    simp only [List.map_map, Function.comp_def, Formula.eval_read]
  rw [← reads]
  rcases hg with hop | hop | hop
  · simp [Formula.fromGate, hop, GateOp.eval, Formula.eval_and]
  · simp [Formula.fromGate, hop, GateOp.eval, Formula.eval_or]
  · simp only [Formula.fromGate, hop, GateOp.eval, Formula.eval]
    cases g.inputs.map (Formula.read wires) <;> rfl

def Formula.expandGate (wires : List Formula) (g : Gate) : List Formula :=
  wires ++ [Formula.fromGate wires g]

def effectiveInputs (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def isNegation (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

/-- A live dependency must name a wire that already exists. -/
def consumes (gates : List Gate) (n a b : Nat) : Prop :=
  a < b ∧ n ≤ b ∧ ∃ g, gates[b - n]? = some g ∧ a ∈ effectiveInputs g

def negatesWire (gates : List Gate) (n b : Nat) : Bool :=
  (gates[b - n]?.map isNegation).getD false

private theorem Formula.polarity_in_and (args : List Formula) (a : Nat) (sign : Bool)
    (path : (args.foldr Formula.and (.constant true)).hasPolarity a sign) :
    ∃ f ∈ args, f.hasPolarity a sign := by
  induction args with
  | nil => exact path.elim
  | cons f fs ih =>
    rcases path with atHead | atTail
    · exact ⟨f, by simp, atHead⟩
    · obtain ⟨t, ht, hpath⟩ := ih atTail
      exact ⟨t, List.mem_cons_of_mem f ht, hpath⟩

private theorem Formula.polarity_in_or (args : List Formula) (a : Nat) (sign : Bool)
    (path : (args.foldr Formula.or (.constant false)).hasPolarity a sign) :
    ∃ f ∈ args, f.hasPolarity a sign := by
  induction args with
  | nil => exact path.elim
  | cons f fs ih =>
    rcases path with atHead | atTail
    · exact ⟨f, by simp, atHead⟩
    · obtain ⟨t, ht, hpath⟩ := ih atTail
      exact ⟨t, List.mem_cons_of_mem f ht, hpath⟩

private theorem Formula.polarity_in_source (wires : List Formula) (g : Gate) (a : Nat) (sign : Bool)
    (hg : supported g) (path : (Formula.fromGate wires g).hasPolarity a sign) :
    ∃ j ∈ effectiveInputs g, (Formula.read wires j).hasPolarity a (if isNegation g then !sign else sign) := by
  rcases hg with hop | hop | hop
  · have h := Formula.polarity_in_and _ a sign (by simpa [Formula.fromGate, hop] using path)
    obtain ⟨f, hf, hp⟩ := h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    exact ⟨j, by simpa [effectiveInputs, hop] using hj, by simpa [isNegation, hop] using hp⟩
  · have h := Formula.polarity_in_or _ a sign (by simpa [Formula.fromGate, hop] using path)
    obtain ⟨f, hf, hp⟩ := h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    exact ⟨j, by simpa [effectiveInputs, hop] using hj, by simpa [isNegation, hop] using hp⟩
  · cases h : g.inputs with
    | nil => simp [Formula.fromGate, hop, h, Formula.hasPolarity] at path
    | cons j js =>
      exact ⟨j, by simp [effectiveInputs, hop, h],
        by simpa [Formula.fromGate, hop, h, isNegation, Formula.hasPolarity] using path⟩

/-- Expand a circuit while treating selected gate wires as new inputs. -/
def Formula.expandWithCuts (cut : Nat → Bool) (wires : List Formula) (gate : Gate) : List Formula :=
  if cut wires.length then wires ++ [.input wires.length] else Formula.expandGate wires gate

def unfoldWithCuts (C : Circuit) (n : Nat) (cut : Nat → Bool) (wire : Nat) : Formula :=
  Formula.read (C.gates.foldl (Formula.expandWithCuts cut)
    (List.ofFn (fun i : Fin n => Formula.input i.val))) wire

private def advanceValues (values : List Bool) (g : Gate) : List Bool :=
  values ++ [g.op.eval (g.inputs.map (fun i => values.getD i false))]

private theorem advance_prefix (gs : List Gate) (values : List Bool) :
    ∃ tail, gs.foldl advanceValues values = values ++ tail := by
  induction gs generalizing values with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨tail, eq⟩ := ih (advanceValues values g)
    refine ⟨g.op.eval (g.inputs.map (fun i => values.getD i false)) :: tail, ?_⟩
    simpa [List.foldl_cons, advanceValues, List.append_assoc] using eq

private theorem value_at_next_wire (g : Gate) (gs : List Gate) (values : List Bool) :
    (gs.foldl advanceValues (advanceValues values g)).getD values.length false =
      g.op.eval (g.inputs.map (fun i => values.getD i false)) := by
  obtain ⟨tail, h⟩ := advance_prefix gs (advanceValues values g)
  rw [h]
  simp [advanceValues, List.append_assoc, List.getD_eq_getElem?_getD]

private theorem eval_cut_trace (cut : Nat → Bool) (gs : List Gate) (wires : List Formula)
    (values full : List Bool) (support : ∀ g ∈ gs, supported g)
    (agrees : wires.map (Formula.eval (fun i => full.getD i false)) = values)
    (finished : gs.foldl advanceValues values = full) :
    (gs.foldl (Formula.expandWithCuts cut) wires).map (Formula.eval (fun i => full.getD i false)) =
      full := by
  induction gs generalizing values wires with
  | nil => simpa using agrees.trans finished
  | cons g rest ih =>
    rw [List.foldl_cons]
    apply ih (values := advanceValues values g) _
    · exact fun next h => support next (List.mem_cons_of_mem g h)
    · have nextIndex : wires.length = values.length := by
        rw [← agrees, List.length_map]
      by_cases cutHere : cut wires.length = true
      · have value := value_at_next_wire g rest values
        rw [show rest.foldl advanceValues (advanceValues values g) = full from finished] at value
        rw [Formula.expandWithCuts, ite_eq_left cutHere]
        simp only [List.map_append, List.map_cons, Formula.eval, List.map_nil]
        rw [agrees, nextIndex, value]
        rfl
      · rw [Formula.expandWithCuts, ite_eq_right cutHere]
        simp only [Formula.expandGate, List.map_append, List.map_cons, List.map_nil]
        rw [Formula.eval_fromGate _ _ _ (support g (by simp)), agrees]
        rfl
    · exact finished

/-- Cutting wires preserves the output when each cut is assigned its
original value. This is independent of how the cuts were selected. -/
theorem eval_unfoldWithCuts (C : Circuit) (n : Nat) (x : Fin n → Bool)
    (cut : Nat → Bool) (wire : Nat) (support : ∀ g ∈ C.gates, supported g) :
    (unfoldWithCuts C n cut wire).eval (fun j => (C.wires (List.ofFn x)).getD j false) =
      (C.wires (List.ofFn x)).getD wire false := by
  let initial := List.ofFn (fun i : Fin n => Formula.input i.val)
  let input := List.ofFn x
  let full := C.wires input
  have done : C.gates.foldl advanceValues input = full := rfl
  obtain ⟨tail, prefixEq⟩ := advance_prefix C.gates input
  rw [done] at prefixEq
  have agrees : initial.map (Formula.eval (fun j => full.getD j false)) = input := by
    simp only [initial, List.map_ofFn, Function.comp_def, Formula.eval]
    congr 1
    funext i
    have bound : i.val < input.length := by simp [input]
    rw [prefixEq, List.getD_eq_getElem?_getD, List.getElem?_append_left bound]
    simp [input, i.isLt]
  change (Formula.read (C.gates.foldl (Formula.expandWithCuts cut) initial) wire).eval
      (fun j => full.getD j false) = full.getD wire false
  rw [Formula.eval_read, eval_cut_trace cut _ _ input full support agrees done]

/-- Paths after symbolic cuts cannot enter a cut wire. -/
def cutEdge (gates : List Gate) (n : Nat) (cut : Nat → Bool) (a b : Nat) : Prop :=
  consumes gates n a b ∧ cut b = false

def CutTrace (gates : List Gate) (n : Nat) (cut : Nat → Bool) (wires : List Formula) : Prop :=
  ∀ j f, wires[j]? = some f → ∀ a sign, f.hasPolarity a sign →
    (a < n ∨ cut a = true) ∧ SignedPath (cutEdge gates n cut) (negatesWire gates n) j a sign

private theorem cutTrace_initial (gates : List Gate) (n : Nat) (cut : Nat → Bool) :
    CutTrace gates n cut (List.ofFn (fun i : Fin n => Formula.input i.val)) := by
  intro j f h a sign hp
  simp only [List.getElem?_ofFn] at h
  split at h
  · cases h
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨Or.inl (by assumption), .done⟩
  · simp at h

private theorem cutTrace_expand (gates : List Gate) (n : Nat) (cut : Nat → Bool)
    (wires : List Formula) (g : Gate) (trace : CutTrace gates n cut wires)
    (lo : n ≤ wires.length) (atGate : gates[wires.length - n]? = some g) (hg : supported g) :
    CutTrace gates n cut (Formula.expandWithCuts cut wires g) := by
  intro j f h a sign hp
  have hstore : ∃ last, Formula.expandWithCuts cut wires g = wires ++ [last] := by
    cases hc : cut wires.length <;> simp [Formula.expandWithCuts, Formula.expandGate, hc]
  by_cases before : j < wires.length
  · obtain ⟨last, eq⟩ := hstore
    apply trace j f _ a sign hp
    simpa [eq, List.getElem?_append_left before] using h
  · have eq : j = wires.length := by
      obtain ⟨last, hs⟩ := hstore
      rw [hs] at h
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h
      simp at bound
      omega
    subst j
    cases hc : cut wires.length
    · have fIsGate : f = Formula.fromGate wires g := by
        simpa [Formula.expandWithCuts, hc, Formula.expandGate, List.getElem?_append_right] using h.symm
      subst f
      obtain ⟨src, hsrc, hpath⟩ := Formula.polarity_in_source wires g a sign hg hp
      have srcExists : src < wires.length := by
        by_cases existsWire : src < wires.length
        · exact existsWire
        · rw [Formula.read, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hpath
          exact hpath.elim
      have readIsSome : wires[src]? = some (Formula.read wires src) := by
        simp [Formula.read, List.getElem?_eq_getElem srcExists, List.getD_eq_getElem?_getD]
      obtain ⟨allowed, path⟩ := trace src _ readIsSome a _ hpath
      have edge : cutEdge gates n cut src wires.length := ⟨⟨srcExists, lo, g, atGate, hsrc⟩, hc⟩
      have finished := path.snoc edge
      refine ⟨allowed, ?_⟩
      cases hn : isNegation g <;> cases sign <;>
        simpa [negatesWire, atGate, hn] using finished
    · have fIsInput : f = .input wires.length := by
        simpa [Formula.expandWithCuts, hc, List.getElem?_append_right] using h.symm
      subst f
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨Or.inr hc, .done⟩

private theorem expandWithCuts_length (cut : Nat → Bool) (wires : List Formula) (g : Gate) :
    (Formula.expandWithCuts cut wires g).length = wires.length + 1 := by
  cases h : cut wires.length <;> simp [Formula.expandWithCuts, Formula.expandGate, h]

private theorem cutTrace_fold (gates : List Gate) (n : Nat) (cut : Nat → Bool)
    (wires : List Formula) (rest : List Gate) (trace : CutTrace gates n cut wires)
    (lo : n ≤ wires.length) (lookup : ∀ k, gates[wires.length - n + k]? = rest[k]?)
    (support : ∀ g ∈ rest, supported g) :
    CutTrace gates n cut (rest.foldl (Formula.expandWithCuts cut) wires) := by
  induction rest generalizing wires with
  | nil => exact trace
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih
    · exact cutTrace_expand gates n cut wires g trace lo
        (by simpa using lookup 0) (support g (by simp))
    · rw [expandWithCuts_length]
      omega
    · intro k
      rw [expandWithCuts_length]
      simpa [show wires.length + 1 - n + k = wires.length - n + (k + 1) by omega] using lookup (k + 1)
    · intro h hh
      exact support h (List.mem_cons_of_mem g hh)

/-- Any variable of a cut expression originates at an original input or a cut
wire and is connected by a path that does not enter a cut. -/
theorem trace_unfoldWithCuts (C : Circuit) (n : Nat) (cut : Nat → Bool) (wire a : Nat)
    (sign : Bool) (support : ∀ g ∈ C.gates, supported g)
    (polarity : (unfoldWithCuts C n cut wire).hasPolarity a sign) :
    (a < n ∨ cut a = true) ∧
      SignedPath (cutEdge C.gates n cut) (negatesWire C.gates n) wire a sign := by
  let initial := List.ofFn (fun i : Fin n => Formula.input i.val)
  let wires := C.gates.foldl (Formula.expandWithCuts cut) initial
  have tr : CutTrace C.gates n cut wires := cutTrace_fold C.gates n cut initial C.gates
    (cutTrace_initial C.gates n cut) (by simp [initial]) (by simp [initial]) support
  have existsWire : wire < wires.length := by
    by_cases h : wire < wires.length
    · exact h
    · change (Formula.read wires wire).hasPolarity a sign at polarity
      rw [Formula.read, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at polarity
      exact polarity.elim
  apply tr wire (Formula.read wires wire) _ a sign polarity
  simp [Formula.read, List.getElem?_eq_getElem existsWire, List.getD_eq_getElem?_getD]

theorem Formula.eval_le_of_signed_le (f : Formula) (x y : Nat → Bool)
    (h : ∀ a sign, f.hasPolarity a sign → if sign then x a ≤ y a else y a ≤ x a) :
    f.eval x ≤ f.eval y := by
  induction f generalizing x y with
  | input a => exact h a true ⟨rfl, rfl⟩
  | constant v => exact le_rfl
  | and a b ihA ihB =>
    have ha := ihA x y (fun j s hp => h j s (Or.inl hp))
    have hb := ihB x y (fun j s hp => h j s (Or.inr hp))
    cases e₁ : a.eval x <;> cases e₂ : a.eval y <;>
      cases e₃ : b.eval x <;> cases e₄ : b.eval y <;> simp_all [Formula.eval]
  | or a b ihA ihB =>
    have ha := ihA x y (fun j s hp => h j s (Or.inl hp))
    have hb := ihB x y (fun j s hp => h j s (Or.inr hp))
    cases e₁ : a.eval x <;> cases e₂ : a.eval y <;>
      cases e₃ : b.eval x <;> cases e₄ : b.eval y <;> simp_all [Formula.eval]
  | not a ih =>
    have ha := ih y x (fun j s hp => by
      have hp' : (Formula.not a).hasPolarity j (!s) := by cases s <;> exact hp
      have hs := h j (!s) hp'
      cases s <;> exact hs)
    cases e₁ : a.eval x <;> cases e₂ : a.eval y <;> simp_all [Formula.eval]

theorem Formula.eval_eq_of_support_eq (f : Formula) (x y : Nat → Bool)
    (h : ∀ a sign, f.hasPolarity a sign → x a = y a) : f.eval x = f.eval y := by
  apply le_antisymm
  · apply f.eval_le_of_signed_le
    intro a sign hp
    rw [h a sign hp]
    cases sign <;> simp
  · apply f.eval_le_of_signed_le
    intro a sign hp
    rw [h a sign hp]
    cases sign <;> simp

private theorem originalValue (C : Circuit) (n : Nat) (x : Fin n → Bool) {a : Nat}
    (ha : a < n) :
    (C.wires (List.ofFn x)).getD a false = x ⟨a, ha⟩ := by
  obtain ⟨tail, h⟩ := advance_prefix C.gates (List.ofFn x)
  change C.wires (List.ofFn x) = List.ofFn x ++ tail at h
  have bound : a < (List.ofFn x).length := by simpa using ha
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_append_left bound]
  simp [ha]

def unfoldOutput (C : Circuit) (n : Nat) : Formula :=
  unfoldWithCuts C n (fun _ => false) C.output

theorem eval_unfoldOutput (C : Circuit) (n : Nat) (x : Nat → Bool)
    (support : ∀ g ∈ C.gates, supported g) :
    (unfoldOutput C n).eval x = C.eval (List.ofFn (fun i : Fin n => x i.val)) := by
  let input (i : Fin n) := x i.val
  refine ((unfoldOutput C n).eval_eq_of_support_eq x
    (fun a => (C.wires (List.ofFn input)).getD a false) ?_).trans
    (eval_unfoldWithCuts C n input (fun _ => false) C.output support)
  intro a sign h
  have ha : a < n := by
    simpa using (trace_unfoldWithCuts C n (fun _ => false) C.output a sign support h).1
  exact (originalValue C n input ha).symm

theorem circuit_polarity (C : Circuit) (n i : Nat) (x y : Nat → Bool)
    (hC : ∀ g ∈ C.gates, supported g)
    (agree : ∀ j, j ≠ i → x j = y j) (hi : y i = true)
    (positive : Bool) (hx : C.eval (List.ofFn (fun j : Fin n => x j.val)) = !positive)
    (hy : C.eval (List.ofFn (fun j : Fin n => y j.val)) = positive) :
    (unfoldOutput C n).hasPolarity i positive :=
  Formula.polarity_of_change (unfoldOutput C n) x y i agree hi positive
    ((eval_unfoldOutput C n x hC).trans hx) ((eval_unfoldOutput C n y hC).trans hy)

theorem trace_circuit_polarity (C : Circuit) (n a : Nat) (sign : Bool)
    (support : ∀ g ∈ C.gates, supported g)
    (polarity : (unfoldOutput C n).hasPolarity a sign) :
    SignedPath (consumes C.gates n) (negatesWire C.gates n) C.output a sign := by
  have tr := (trace_unfoldWithCuts C n (fun _ => false) C.output a sign support polarity).2
  have edgeEq : cutEdge C.gates n (fun _ => false) = consumes C.gates n := by
    funext u v
    simp [cutEdge]
  simpa only [edgeEq] using tr

def inputRow (r : Nat) : List Bool := List.ofFn (fun i : Fin 6 => r.testBit i.val)

def realizesGraph (C : Circuit) : Prop :=
  ∀ i j : Fin 6, C.eval (List.ofFn (fun k : Fin 6 => decide (k = i ∨ k = j))) =
    (274910143 : Nat).testBit (6 * min i.val j.val + max i.val j.val)

theorem eval_promised_row (C : Circuit) (realizes : realizesGraph C) {r : Nat}
    (hr : r ∈ rows) : C.eval (inputRow r) = target r := by
  have bound : r < 64 := by
    simp [rows] at hr
    omega
  have checked : ∀ v : Fin 64, v.val ∈ rows →
      ∃ i j : Fin 6,
        inputRow v.val = List.ofFn (fun k : Fin 6 => decide (k = i ∨ k = j)) ∧
        target v.val = (274910143 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
    decide +kernel
  obtain ⟨i, j, in_eq, out_eq⟩ := checked ⟨r, bound⟩ hr
  rw [in_eq, out_eq]
  exact realizes i j

private theorem row_toggle_agrees (r i : Nat) :
    ∀ j, j ≠ i → r.testBit j = (r ||| (2 ^ i)).testBit j := by
  intro j h
  rw [Nat.testBit_or, Nat.testBit_two_pow_of_ne (Ne.symm h)]
  simp

private theorem row_toggle_high (r i : Nat) : (r ||| (2 ^ i)).testBit i = true := by
  rw [Nat.testBit_or, Nat.testBit_two_pow_self]
  simp

/-- Every essential input lies on some signed path to the actual output. -/
theorem circuit_essential_path (C : Circuit) (hC : ∀ g ∈ C.gates, supported g)
    (realizes : realizesGraph C) (i : Fin 6) (hi : i ≠ 3) :
    ∃ sign : Bool, (unfoldOutput C 6).hasPolarity i.val sign := by
  obtain ⟨r, ⟨hr, _, hr'⟩, differ⟩ := five_essential i hi
  let s := r.val ||| (2 ^ i.val)
  refine ⟨target s, circuit_polarity C 6 i.val (fun j => r.val.testBit j) (fun j => s.testBit j)
    hC (row_toggle_agrees r.val i.val) (row_toggle_high r.val i.val) _ ?_ ?_⟩
  · rw [show List.ofFn (fun j : Fin 6 => r.val.testBit j.val) = inputRow r.val by rfl]
    rw [eval_promised_row C realizes hr]
    change target r.val ≠ target s at differ
    cases a : target r.val <;> cases b : target s <;> simp_all
  · exact eval_promised_row C realizes hr'

/-- Inputs 1 and 2 must each reach the output through both polarities. -/
theorem circuit_binate_paths (C : Circuit) (hC : ∀ g ∈ C.gates, supported g)
    (realizes : realizesGraph C) (i : Fin 6) (hi : i = 1 ∨ i = 2) :
    (unfoldOutput C 6).hasPolarity i.val true ∧
    (unfoldOutput C 6).hasPolarity i.val false := by
  obtain ⟨rise, fall, ⟨hr, _, hr'⟩, ⟨hf, _, hf'⟩, rise0, rise1, fall1, fall0⟩ := two_binates i hi
  constructor
  · exact circuit_polarity C 6 i.val (fun j => rise.val.testBit j)
      (fun j => (rise.val ||| (2 ^ i.val)).testBit j) hC
      (row_toggle_agrees rise.val i.val) (row_toggle_high rise.val i.val) true
      ((eval_promised_row C realizes hr).trans rise0) ((eval_promised_row C realizes hr').trans rise1)
  · exact circuit_polarity C 6 i.val (fun j => fall.val.testBit j)
      (fun j => (fall.val ||| (2 ^ i.val)).testBit j) hC
      (row_toggle_agrees fall.val i.val) (row_toggle_high fall.val i.val) false
      ((eval_promised_row C realizes hf).trans fall1) ((eval_promised_row C realizes hf').trans fall0)

/-- If an actual circuit has just one branching wire along paths to its
output, both of the binate inputs have a path to that wire. -/
theorem actual_input_reaches_shared (C : Circuit) (support : ∀ g ∈ C.gates, supported g)
    (realizes : realizesGraph C) (i : Fin 6) (hi : i = 1 ∨ i = 2) (shared : Nat)
    (unique : ∀ v l r, l ≠ r → consumes C.gates 6 v l → consumes C.gates 6 v r →
      v = shared) :
    ∃ sign, SignedPath (consumes C.gates 6) (negatesWire C.gates 6) shared i.val sign := by
  obtain ⟨pos, neg⟩ := circuit_binate_paths C support realizes i hi
  exact (trace_circuit_polarity C 6 i.val true support pos).reaches_unique_branch
    (trace_circuit_polarity C 6 i.val false support neg) (fun _ _ edge => edge.1) unique

open scoped BigOperators

/-- A path to a live gate also reaches the output. -/
def liveWire (C : Circuit) (w : Nat) : Prop :=
  ∃ sign, SignedPath (consumes C.gates 6) (negatesWire C.gates 6) C.output w sign

def liveEdge (C : Circuit) (a b : Nat) : Prop := consumes C.gates 6 a b ∧ liveWire C b

theorem SignedPath.to_live (C : Circuit) {a : Nat} {sign : Bool}
    (p : SignedPath (consumes C.gates 6) (negatesWire C.gates 6) C.output a sign) :
    SignedPath (liveEdge C) (negatesWire C.gates 6) C.output a sign := by
  induction p with
  | done => exact .done
  | next edge tail ih => exact .next ⟨edge, _, tail⟩ ih

theorem SignedPath.last_edge {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {sign : Bool} (p : SignedPath edge negates root a sign) (hne : a ≠ root) :
    ∃ b, edge b root := by
  induction p with
  | done => exact (hne rfl).elim
  | @next a b sign link tail ih =>
    by_cases h : b = root
    · subst b
      exact ⟨a, link⟩
    · exact ih h

theorem SignedPath.negative_gate {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {sign : Bool} (p : SignedPath edge negates root a sign) (negative : sign = false) :
    ∃ u v, edge u v ∧ negates v = true ∧ ∃ s, SignedPath edge negates root v s := by
  induction p with
  | done => simp at negative
  | @next a b sign link tail ih =>
    cases hn : negates b
    · apply ih
      simpa [hn] using negative
    · exact ⟨a, b, link, hn, _, tail⟩

/-- A negative path passes through a NOT, whose wire is reachable from
the starting vertex. -/
theorem SignedPath.reaches_negation {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {sign : Bool} (p : SignedPath edge negates root a sign) (negative : sign = false)
    (forward : ∀ a b, edge a b → a < b) :
    ∃ u v, edge u v ∧ negates v = true ∧ a < v ∧
      (∃ tailSign, SignedPath edge negates root v tailSign) ∧
      ∃ preSign, SignedPath edge negates v a preSign := by
  induction p with
  | done => simp at negative
  | @next a b sign link tail ih =>
    cases hn : negates b with
    | false =>
      obtain ⟨u, v, e, h, later, q, _, path⟩ := ih (by simpa [hn] using negative)
      exact ⟨u, v, e, h, Nat.lt_trans (forward a b link) later, q, _, .next link path⟩
    | true => exact ⟨_, b, link, hn, forward a b link, ⟨_, tail⟩, _, .next link .done⟩

noncomputable def liveWires (C : Circuit) : Finset Nat := by
  classical
  exact (Finset.range (6 + C.gates.length)).filter (liveWire C)

theorem consuming_gate_bounded (C : Circuit) {a b : Nat} (e : consumes C.gates 6 a b) :
    b < 6 + C.gates.length := by
  obtain ⟨_, six, g, hg, _⟩ := e
  have hi : b - 6 < C.gates.length := by
    by_cases hi : b - 6 < C.gates.length
    · exact hi
    · rw [List.getElem?_eq_none (by omega)] at hg
      contradiction
  omega

theorem liveWires_iff (C : Circuit) (rootBound : C.output < 6 + C.gates.length) (a : Nat) :
    a ∈ liveWires C ↔ liveWire C a := by
  classical
  simp only [liveWires, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · rintro ⟨sign, path⟩
    have le := path.start_le (fun _ _ edge => edge.1)
    exact ⟨by omega, sign, path⟩

theorem realizing_output_bounded (C : Circuit) (support : ∀ g ∈ C.gates, supported g)
    (realizes : realizesGraph C) : C.output < 6 + C.gates.length := by
  obtain ⟨_, p⟩ := circuit_binate_paths C support realizes 1 (by decide)
  have path := trace_circuit_polarity C 6 1 false support p
  have different : (1 : Nat) ≠ C.output := by
    intro eq
    have positive := (circuit_binate_paths C support realizes 2 (by decide)).1
    have otherPath := trace_circuit_polarity C 6 2 true support positive
    have order := otherPath.start_le (fun _ _ edge => edge.1)
    omega
  obtain ⟨_, link⟩ := path.last_edge different
  exact consuming_gate_bounded C link

noncomputable def predecessors (C : Circuit) (b : Nat) : Finset Nat := by
  classical
  exact (liveWires C).filter (fun a => consumes C.gates 6 a b)

noncomputable def usersOf (C : Circuit) (a : Nat) : Finset Nat := by
  classical
  exact (liveWires C).filter (consumes C.gates 6 a)

theorem equal_edge_totals (C : Circuit) :
    ∑ b ∈ liveWires C, (predecessors C b).card =
      ∑ a ∈ liveWires C, (usersOf C a).card := by
  classical
  simp only [predecessors, usersOf, Finset.card_filter]
  exact Finset.sum_comm

theorem predecessor_bound (C : Circuit) (g : Gate) {b : Nat}
    (lookup : C.gates[b - 6]? = some g) :
    (predecessors C b).card ≤ (effectiveInputs g).length := by
  classical
  calc
    _ ≤ (effectiveInputs g).toFinset.card := Finset.card_le_card (by
      intro a ha
      obtain ⟨_, _, gate, atGate, hs⟩ := (Finset.mem_filter.mp ha).2
      have eq : gate = g := Option.some.inj (atGate.symm.trans lookup)
      exact List.mem_toFinset.mpr (eq ▸ hs))
    _ ≤ _ := List.toFinset_card_le _

theorem predecessor_bound_two (C : Circuit) (fanIn : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (b : Nat) : (predecessors C b).card ≤ if b < 6 then 0 else 2 := by
  classical
  cases h : C.gates[b - 6]? with
  | none =>
    have empty : predecessors C b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨_, _, g, hgate, _⟩ := (Finset.mem_filter.mp ha).2
      rw [h] at hgate
      contradiction
    simp [empty]
  | some g =>
    by_cases lo : b < 6
    · have empty : predecessors C b = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have ge := (Finset.mem_filter.mp ha).2.2.1
        omega
      simp [empty]
    · have hg : g ∈ C.gates := List.mem_of_getElem? h
      have lengthLe : (effectiveInputs g).length ≤ 2 := by
        have hlen := fanIn g hg
        cases hop : g.op <;> simp [effectiveInputs, hop, List.length_take] <;> omega
      rw [ite_eq_right lo]
      exact (predecessor_bound C g h).trans lengthLe

theorem predecessor_bound_not (C : Circuit) (b : Nat)
    (hn : negatesWire C.gates 6 b = true) : (predecessors C b).card ≤ 1 := by
  cases h : C.gates[b - 6]? with
  | none => simp [negatesWire, h] at hn
  | some g =>
    have isNot : g.op = .not := by
      cases hop : g.op <;> simp_all [negatesWire, isNegation]
    exact (predecessor_bound C g h).trans (by simp [effectiveInputs, isNot, List.length_take])

theorem root_has_no_live_user (C : Circuit) : usersOf C C.output = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have parts : b ∈ liveWires C ∧ consumes C.gates 6 C.output b := Finset.mem_filter.mp hb
  have live : liveWire C b := (Finset.mem_filter.mp parts.1).2
  obtain ⟨_, suffix⟩ := live
  have h := suffix.start_le (fun _ _ e => e.1)
  exact Nat.not_lt_of_ge h parts.2.1

theorem live_wire_is_used (C : Circuit) (limit : C.output < 6 + C.gates.length)
    {a : Nat} (ha : a ∈ (liveWires C).erase C.output) : 1 ≤ (usersOf C a).card := by
  classical
  obtain ⟨neq, liveA⟩ := Finset.mem_erase.mp ha
  obtain ⟨_, path⟩ := (liveWires_iff C limit a).mp liveA
  have witness : (usersOf C a).Nonempty := by
    cases path with
    | done => exact (neq rfl).elim
    | @next _ b _ edge tail =>
      exact ⟨b, Finset.mem_filter.mpr ⟨(liveWires_iff C limit b).mpr ⟨_, tail⟩, edge⟩⟩
  exact Finset.Nonempty.card_pos witness

theorem branching_has_two_users (C : Circuit) (limit : C.output < 6 + C.gates.length)
    {a b c : Nat} (separate : b ≠ c) (left : liveEdge C a b) (right : liveEdge C a c) :
    2 ≤ (usersOf C a).card := by
  classical
  have contained : ({b, c} : Finset Nat) ⊆ usersOf C a := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_filter.mpr ⟨(liveWires_iff C limit _).mpr left.2, left.1⟩
    · rcases Finset.mem_singleton.mp hd with rfl
      exact Finset.mem_filter.mpr ⟨(liveWires_iff C limit _).mpr right.2, right.1⟩
  simpa [separate] using Finset.card_le_card contained

theorem count_live_inputs (C : Circuit) (support : ∀ g ∈ C.gates, supported g)
    (realizes : realizesGraph C) (limit : C.output < 6 + C.gates.length) :
    5 ≤ ((liveWires C).filter (fun w => w < 6)).card := by
  classical
  have each (i : Fin 6) (ne : i ≠ 3) : i.val ∈ (liveWires C).filter (fun w => w < 6) := by
    obtain ⟨s, path⟩ := circuit_essential_path C support realizes i ne
    exact Finset.mem_filter.mpr
      ⟨(liveWires_iff C limit i.val).mpr ⟨s, trace_circuit_polarity C 6 i.val s support path⟩, i.isLt⟩
  have sub : ({0, 1, 2, 4, 5} : Finset Nat) ⊆ (liveWires C).filter (fun w => w < 6) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact each 0 (by decide)
    · exact each 1 (by decide)
    · exact each 2 (by decide)
    · exact each 4 (by decide)
    · exact each 5 (by decide)
  calc
    5 = ({0, 1, 2, 4, 5} : Finset Nat).card := by decide
    _ ≤ _ := Finset.card_le_card sub

theorem live_gate_count_le (C : Circuit) :
    ((liveWires C).filter (fun w => ¬ w < 6)).card ≤ C.gates.length := by
  classical
  have sub : (liveWires C).filter (fun w => ¬ w < 6) ⊆
      (Finset.range C.gates.length).image (fun j => 6 + j) := by
    intro w hw
    obtain ⟨live, ge⟩ := Finset.mem_filter.mp hw
    have bound : w < 6 + C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp live).1
    exact Finset.mem_image.mpr ⟨w - 6, Finset.mem_range.mpr (by omega), by omega⟩
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (by simp))

/-- Every non-output live wire pays one use. The remaining uses of any
marked live wires are included in the total. -/
theorem live_repeat_budget (C : Circuit) (limit : C.output < 6 + C.gates.length)
    (marked : Finset Nat) (sub : marked ⊆ (liveWires C).erase C.output) :
    (liveWires C).card - 1 + ∑ x ∈ marked, ((usersOf C x).card - 1) ≤
      ∑ x ∈ liveWires C, (usersOf C x).card := by
  classical
  let V := liveWires C
  let R := V.erase C.output
  let extra (x : Nat) := (usersOf C x).card - 1
  have rootIn : C.output ∈ V := (liveWires_iff C limit _).mpr ⟨true, .done⟩
  have total := Finset.sum_erase_add V (fun x => (usersOf C x).card) rootIn
  rw [root_has_no_live_user C, Finset.card_empty, Nat.add_zero] at total
  have count : R.card = V.card - 1 := Finset.card_erase_of_mem rootIn
  have sum : R.card + ∑ x ∈ R, extra x = ∑ x ∈ R, (usersOf C x).card := by
    calc
      R.card + ∑ x ∈ R, extra x = ∑ x ∈ R, (1 + extra x) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = _ := Finset.sum_congr rfl fun x hx => by
        have used := live_wire_is_used C limit hx
        dsimp [extra]
        omega
  have extraBound : ∑ x ∈ marked, extra x ≤ ∑ x ∈ R, extra x :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
  change (∑ x ∈ R, (usersOf C x).card) = ∑ x ∈ V, (usersOf C x).card at total
  change V.card - 1 + ∑ x ∈ marked, extra x ≤ ∑ x ∈ V, (usersOf C x).card
  omega

theorem edges_bounded_by_gates (C : Circuit) (fanIn : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (limit : C.output < 6 + C.gates.length) {nGate : Nat} (liveN : liveWire C nGate)
    (isGate : 6 ≤ nGate) (isNot : negatesWire C.gates 6 nGate = true) :
    (∑ x ∈ liveWires C, (usersOf C x).card) + 1 ≤
      2 * ((liveWires C).filter (fun w => ¬ w < 6)).card := by
  classical
  let V := liveWires C
  let J := V.filter (fun w => ¬ w < 6)
  let upper (x : Nat) := if x < 6 then 0 else 2
  have notIn : nGate ∈ V := (liveWires_iff C limit _).mpr liveN
  have less := predecessor_bound_not C nGate isNot
  have upperHere : upper nGate = 2 := by simp [upper, Nat.not_lt_of_ge isGate]
  have totalUpper : (∑ x ∈ V, upper x) = 2 * J.card := by
    have equal : (∑ x ∈ V, upper x) = ∑ x ∈ V, (if ¬ x < 6 then (2 : Nat) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x < 6 <;> simp [upper, hx]
    rw [equal, ← Finset.sum_filter]
    simp [J, Nat.mul_comm]
  have part : (∑ x ∈ V.erase nGate, (predecessors C x).card) ≤
      ∑ x ∈ V.erase nGate, upper x := by
    exact Finset.sum_le_sum (fun x _ => predecessor_bound_two C fanIn x)
  have predSplit := Finset.sum_erase_add V (fun x => (predecessors C x).card) notIn
  have upperSplit := Finset.sum_erase_add V upper notIn
  change _ + 1 ≤ 2 * J.card
  rw [← equal_edge_totals]
  change (∑ x ∈ V, (predecessors C x).card) + 1 ≤ 2 * J.card
  omega

/-- Pointwise equality follows when the predecessor budget is tight. -/
theorem tight_predecessor_budget (C : Circuit) (fanIn : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (limit : C.output < 6 + C.gates.length) {nGate : Nat} (liveN : liveWire C nGate)
    (isGate : 6 ≤ nGate) (isNot : negatesWire C.gates 6 nGate = true)
    (tight : (∑ x ∈ liveWires C, (usersOf C x).card) + 1 =
      2 * ((liveWires C).filter (fun w => ¬ w < 6)).card) :
    ∀ x ∈ liveWires C, (predecessors C x).card =
      if x = nGate then 1 else if x < 6 then 0 else 2 := by
  classical
  let V := liveWires C
  let cap (x : Nat) := if x = nGate then 1 else if x < 6 then 0 else 2
  let upper (x : Nat) := if x < 6 then 0 else 2
  have nIn : nGate ∈ V := (liveWires_iff C limit _).mpr liveN
  have capBound (x : Nat) : (predecessors C x).card ≤ cap x := by
    by_cases same : x = nGate
    · subst x
      simpa [cap] using predecessor_bound_not C nGate isNot
    · simpa [cap, same] using predecessor_bound_two C fanIn x
  have totalUpper : (∑ x ∈ V, upper x) =
      2 * (V.filter (fun w => ¬ w < 6)).card := by
    have equal : (∑ x ∈ V, upper x) = ∑ x ∈ V, (if ¬ x < 6 then (2 : Nat) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x < 6 <;> simp [upper, hx]
    rw [equal, ← Finset.sum_filter]
    simp [Nat.mul_comm]
  have sameRest : ∑ x ∈ V.erase nGate, cap x = ∑ x ∈ V.erase nGate, upper x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [cap, upper, (Finset.mem_erase.mp hx).1]
  have capSum := Finset.sum_erase_add V cap nIn
  have upperSum := Finset.sum_erase_add V upper nIn
  have capAt : cap nGate = 1 := by simp [cap]
  have upperAt : upper nGate = 2 := by simp [upper, Nat.not_lt_of_ge isGate]
  rw [← equal_edge_totals] at tight
  change (∑ x ∈ V, (predecessors C x).card) + 1 =
    2 * (V.filter (fun w => ¬ w < 6)).card at tight
  have totalEq : ∑ x ∈ V, (predecessors C x).card = ∑ x ∈ V, cap x := by omega
  intro x hx
  change (predecessors C x).card = cap x
  have capSplit := Finset.sum_erase_add V cap hx
  have actualSplit := Finset.sum_erase_add V (fun j => (predecessors C j).card) hx
  have partialBound : (∑ j ∈ V.erase x, (predecessors C j).card) ≤
      ∑ j ∈ V.erase x, cap j := Finset.sum_le_sum (fun j _ => capBound j)
  have atX := capBound x
  omega

/-- Six gates, five essential inputs and a negative path leave exactly one
branching wire in the actual live cone. -/
theorem realizing_live_topology (C : Circuit) (support : ∀ g ∈ C.gates, supported g)
    (fanIn : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (size : C.size ≤ 6)
    (realizes : realizesGraph C) :
    ∃ shared nGate,
      (∃ a b, a ≠ b ∧ liveEdge C shared a ∧ liveEdge C shared b) ∧
      SignedPath (liveEdge C) (negatesWire C.gates 6) C.output shared false ∧
      (∀ v l r, l ≠ r → liveEdge C v l → liveEdge C v r → v = shared) ∧
      liveWire C nGate ∧ 6 ≤ nGate ∧ negatesWire C.gates 6 nGate = true ∧
      (∀ w, liveWire C w → 6 ≤ w → negatesWire C.gates 6 w = true → w = nGate) ∧
      ¬ liveWire C 3 := by
  classical
  have limit := realizing_output_bounded C support realizes
  have ⟨pos, neg⟩ := circuit_binate_paths C support realizes 1 (by decide)
  have p := (trace_circuit_polarity C 6 1 true support pos).to_live C
  have q := (trace_circuit_polarity C 6 1 false support neg).to_live C
  obtain ⟨shared, a, b, ne, ab, bb, _, s₁, s₂, _, first, second, different⟩ :=
    p.diverges_with_suffixes q (fun _ _ e => e.1.1) (by decide)
  have negative : SignedPath (liveEdge C) (negatesWire C.gates 6) C.output shared false := by
    cases h : s₁
    · simpa [h] using first
    · have h' : s₂ = false := by cases s₂ <;> simp_all
      simpa [h'] using second
  have sUsed := branching_has_two_users C limit ne ab bb
  have sLive : liveWire C shared := by
    obtain ⟨_, p⟩ := ab.2
    exact ⟨_, .next ab.1 p⟩
  have sNotRoot : shared ≠ C.output := by
    intro eq
    simp [eq, root_has_no_live_user] at sUsed
  have sNotRootIn : shared ∈ (liveWires C).erase C.output :=
    Finset.mem_erase.mpr ⟨sNotRoot, (liveWires_iff C limit _).mpr sLive⟩
  obtain ⟨u, n, edge, isNeg, _⟩ := q.negative_gate rfl
  have upper := edges_bounded_by_gates C fanIn limit edge.2 edge.1.2.1 isNeg
  let V := liveWires C
  let R := V.erase C.output
  let edges := ∑ x ∈ V, (usersOf C x).card
  let gates := ((liveWires C).filter (fun w => ¬ w < 6)).card
  have paid := live_repeat_budget C limit {shared} (Finset.singleton_subset_iff.mpr sNotRootIn)
  simp only [Finset.sum_singleton] at paid
  have lower : V.card ≤ edges := by
    change V.card - 1 + ((usersOf C shared).card - 1) ≤ edges at paid
    omega
  have partition := Finset.card_filter_add_card_filter_not (s := V) (fun w => w < 6)
  have inputCount := count_live_inputs C support realizes limit
  change 5 ≤ (V.filter (fun w => w < 6)).card at inputCount
  change (V.filter (fun w => w < 6)).card + gates = V.card at partition
  change edges + 1 ≤ 2 * gates at upper
  have gSize : gates ≤ 6 := (live_gate_count_le C).trans size
  have eqEdges : edges = V.card := by omega
  have tight : edges + 1 = 2 * gates := by omega
  have countInputs : (V.filter (fun w => w < 6)).card = 5 := by omega
  have noThree : ¬ liveWire C 3 := by
    intro live3
    have each (i : Fin 6) : i.val ∈ V.filter (fun w => w < 6) := by
      by_cases hi : i = 3
      · subst i
        exact Finset.mem_filter.mpr ⟨(liveWires_iff C limit _).mpr live3, by decide⟩
      · obtain ⟨s, path⟩ := circuit_essential_path C support realizes i hi
        exact Finset.mem_filter.mpr
          ⟨(liveWires_iff C limit _).mpr ⟨s, trace_circuit_polarity C 6 i.val s support path⟩, i.isLt⟩
    have contains : Finset.range 6 ⊆ V.filter (fun w => w < 6) :=
      fun v hv => each ⟨v, Finset.mem_range.mp hv⟩
    have h := Finset.card_le_card contains
    simp [countInputs] at h
  have budget := tight_predecessor_budget C fanIn limit edge.2 edge.1.2.1 isNeg tight
  have uniqueNot : ∀ w, liveWire C w → 6 ≤ w → negatesWire C.gates 6 w = true → w = n := by
    intro w live ge hnot
    by_cases hn : w = n
    · exact hn
    · have hb := budget w ((liveWires_iff C limit w).mpr live)
      have hl := predecessor_bound_not C w hnot
      simp only [ite_eq_right hn, ite_eq_right (Nat.not_lt_of_ge ge)] at hb
      omega
  refine ⟨shared, n, ⟨a, b, ne, ab, bb⟩, negative, ?_, edge.2, edge.1.2.1, isNeg, uniqueNot, noThree⟩
  intro v l r separate hl hr
  by_cases same : v = shared
  · exact same
  · have hv := branching_has_two_users C limit separate hl hr
    have vNotRoot : v ≠ C.output := by
      intro eq
      simp [eq, root_has_no_live_user] at hv
    have vLive : liveWire C v := by
      obtain ⟨_, suffix⟩ := hl.2
      exact ⟨_, .next hl.1 suffix⟩
    have vIn : v ∈ R := Finset.mem_erase.mpr ⟨vNotRoot, (liveWires_iff C limit _).mpr vLive⟩
    have marked : ({shared, v} : Finset Nat) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact sNotRootIn
      · exact vIn
    have tooMany := live_repeat_budget C limit {shared, v} marked
    rw [Finset.sum_insert (by simpa using Ne.symm same), Finset.sum_singleton, ← Nat.add_assoc] at tooMany
    change V.card - 1 + ((usersOf C shared).card - 1) + ((usersOf C v).card - 1) ≤
      edges at tooMany
    omega

/-- The shared wire is a gate reached by both binate inputs and lies
upstream of the unique live negation. Input 3 is outside the output cone. -/
theorem realizing_shared_upstream (C : Circuit) (support : ∀ g ∈ C.gates, supported g)
    (fanIn : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (size : C.size ≤ 6)
    (realizes : realizesGraph C) :
    ∃ shared nGate, 6 ≤ shared ∧ shared < nGate ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 →
        ∃ s, SignedPath (liveEdge C) (negatesWire C.gates 6) shared i.val s) ∧
      (∃ s, SignedPath (liveEdge C) (negatesWire C.gates 6) nGate shared s) ∧
      (∀ v l r, l ≠ r → liveEdge C v l → liveEdge C v r → v = shared) ∧
      (∀ w, liveWire C w → 6 ≤ w → negatesWire C.gates 6 w = true → w = nGate) ∧
      liveWire C nGate ∧ negatesWire C.gates 6 nGate = true ∧ ¬ liveWire C 3 := by
  obtain ⟨shared, n, _, negative, unique, liveN, _, negN, uniqueNot, noThree⟩ :=
    realizing_live_topology C support fanIn size realizes
  have forward : ∀ a b, liveEdge C a b → a < b := fun _ _ h => h.1.1
  have reaches (i : Fin 6) (hi : i = 1 ∨ i = 2) :
      ∃ s, SignedPath (liveEdge C) (negatesWire C.gates 6) shared i.val s := by
    obtain ⟨pp, pn⟩ := circuit_binate_paths C support realizes i hi
    have pos := (trace_circuit_polarity C 6 _ true support pp).to_live C
    have neg := (trace_circuit_polarity C 6 _ false support pn).to_live C
    exact pos.reaches_unique_branch neg forward unique
  obtain ⟨_, r1⟩ := reaches 1 (by decide)
  obtain ⟨_, r2⟩ := reaches 2 (by decide)
  have ge : 6 ≤ shared := by
    by_cases eq : (1 : Nat) = shared
    · have ne : (2 : Nat) ≠ shared := by omega
      obtain ⟨_, h⟩ := r2.last_edge ne
      exact h.1.2.1
    · obtain ⟨_, h⟩ := r1.last_edge eq
      exact h.1.2.1
  obtain ⟨_, v, link, hNot, lt, _, reachV⟩ := negative.reaches_negation rfl forward
  have eqNot := uniqueNot v link.2 link.1.2.1 hNot
  exact ⟨shared, n, ge, eqNot ▸ lt, reaches, eqNot ▸ reachV, unique, uniqueNot, liveN, negN, noThree⟩

theorem SignedPath.map_edge {e e' : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {s : Bool} (p : SignedPath e negates root a s)
    (maps : ∀ u v, e u v → e' u v) : SignedPath e' negates root a s := by
  induction p with
  | done => exact .done
  | next link _ ih => exact .next (maps _ _ link) ih

theorem SignedPath.join_path {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root mid a : Nat} {s t : Bool} (p : SignedPath edge negates mid a s)
    (q : SignedPath edge negates root mid t) :
    SignedPath edge negates root a (if t then s else !s) := by
  induction p with
  | done => cases t <;> exact q
  | @next u v sign link tail ih =>
    have joined := SignedPath.next link ih
    cases hn : negates v <;> cases t <;> simpa [hn] using joined

def liveCutEdge (C : Circuit) (cut : Nat → Bool) (a b : Nat) : Prop :=
  liveEdge C a b ∧ cut b = false

/-- When the target is live, every vertex visited by its traced expression
is also live, including in the presence of cuts. -/
theorem SignedPath.to_live_cut (C : Circuit) (cut : Nat → Bool) {target a : Nat} {s : Bool}
    (p : SignedPath (cutEdge C.gates 6 cut) (negatesWire C.gates 6) target a s)
    (ltarget : liveWire C target) :
    SignedPath (liveCutEdge C cut) (negatesWire C.gates 6) target a s := by
  obtain ⟨_, suffix⟩ := ltarget
  induction p with
  | done => exact .done
  | next link tail ih =>
    have mid := tail.map_edge (fun _ _ h => h.1)
    exact .next ⟨⟨link.1, _, mid.join_path suffix⟩, link.2⟩ ih

theorem SignedPath.all_positive {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {s : Bool} (p : SignedPath edge negates root a s)
    (h : ∀ u v, edge u v → negates v = false) : s = true := by
  induction p with
  | done => rfl
  | next link _ ih => simpa [h _ _ link] using ih

theorem SignedPath.into_only_not {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root a : Nat} {s : Bool} (p : SignedPath edge negates root a s)
    (ne : a ≠ root) (isNot : negates root = true)
    (other : ∀ u v, edge u v → v ≠ root → negates v = false)
    (forward : ∀ u v, edge u v → u < v) : s = false := by
  induction p with
  | done => exact (ne rfl).elim
  | @next a b sign link tail ih =>
    by_cases eq : b = root
    · subst b
      cases tail with
      | done => simp [isNot]
      | next edge_t path =>
        have lt := forward _ _ edge_t
        have le := path.start_le forward
        omega
    · simpa [other _ _ link eq] using ih eq

theorem SignedPath.no_enter_cut {edge : Nat → Nat → Prop} {negates : Nat → Bool}
    {root cut a : Nat} {s t : Bool}
    (toCut : SignedPath edge negates cut a s)
    (bypass : SignedPath (fun u v => edge u v ∧ v ≠ cut) negates root a t)
    (startAway : a ≠ cut) (forward : ∀ u v, edge u v → u < v)
    (order : cut ≤ root) (unique : ∀ v l r, l ≠ r → edge v l → edge v r → v = cut) : False := by
  induction toCut generalizing t with
  | done => exact startAway rfl
  | @next u v sign link tail ih =>
    have lt := Nat.lt_of_lt_of_le (forward u v link) (tail.start_le forward)
    cases bypass with
    | done => omega
    | @next _ w other hop tailB =>
      by_cases equal : v = w
      · subst w
        exact ih tailB hop.2
      · exact startAway (unique u v w equal link hop.1)

theorem candidate_topology (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (size : C.size ≤ 6) (realizes : realizesGraph C) :
    ∃ shared nGate, 6 ≤ shared ∧ shared < nGate ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 →
        ∃ s, SignedPath (liveEdge C) (negatesWire C.gates 6) shared i.val s) ∧
      (∃ s, SignedPath (liveEdge C) (negatesWire C.gates 6) nGate shared s) ∧
      (∀ v l r, l ≠ r → liveEdge C v l → liveEdge C v r → v = shared) ∧
      (∀ w, liveWire C w → 6 ≤ w → negatesWire C.gates 6 w = true → w = nGate) ∧
      liveWire C nGate ∧ negatesWire C.gates 6 nGate = true ∧ ¬ liveWire C 3 := by
  apply realizing_shared_upstream C _ _ size realizes
  · intro g hg
    simpa [supported] using (legal g hg).1
  · exact fun g hg => (legal g hg).2

/-- Fix a single-input edge of the promised truth table and recover its sign. -/
theorem promised_signed_path (C : Circuit) (support : ∀ g ∈ C.gates, supported g)
    (realizes : realizesGraph C) (low i : Nat) (s : Bool)
    (hlo : low ∈ rows) (hhi : low ||| (2 ^ i) ∈ rows)
    (vlo : target low = !s) (vhi : target (low ||| (2 ^ i)) = s) :
    SignedPath (liveEdge C) (negatesWire C.gates 6) C.output i s := by
  have p := circuit_polarity C 6 i (fun j => low.testBit j)
      (fun j => (low ||| (2 ^ i)).testBit j) support
      (row_toggle_agrees low i) (row_toggle_high low i) s
      ((eval_promised_row C realizes hlo).trans vlo) ((eval_promised_row C realizes hhi).trans vhi)
  exact (trace_circuit_polarity C 6 i s support p).to_live C

private theorem input_value (C : Circuit) (r a : Nat) (ha : a < 6) :
    (C.wires (inputRow r)).getD a false = r.testBit a :=
  originalValue C 6 (fun i => r.testBit i.val) ha

private theorem reachable_input_live (C : Circuit) {w a : Nat} {s : Bool}
    (p : SignedPath (liveEdge C) (negatesWire C.gates 6) w a s) (live : liveWire C w) :
    liveWire C a := by
  obtain ⟨_, suffix⟩ := live
  exact ⟨_, (p.map_edge (fun _ _ h => h.1)).join_path suffix⟩

theorem SignedPath.positive_below {edge : Nat → Nat → Prop} {neg : Nat → Bool}
    {root a : Nat} {s : Bool} (p : SignedPath edge neg root a s)
    (forward : ∀ x y, edge x y → x < y)
    (positive : ∀ x y, edge x y → y ≤ root → neg y = false) : s = true := by
  induction p with
  | done => rfl
  | next link tail ih => simpa [positive _ _ link (tail.start_le forward)] using ih

set_option maxHeartbeats 4000000 in
theorem no_six_gate_circuit :
    ¬ (∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ realizesGraph C) := by
  rintro ⟨C, legal, size, realizes⟩
  classical
  have support : ∀ g ∈ C.gates, supported g := fun g hg => by simpa [supported] using (legal g hg).1
  obtain ⟨shared, n, geShared, sharedLt, bin, _, unique, uniqueNot, liveN, negN, noThree⟩ :=
    candidate_topology C legal size realizes
  let e := liveEdge C
  let neg := negatesWire C.gates 6
  let reach (a : Nat) : Prop := ∃ s, SignedPath e neg shared a s
  have forward : ∀ a b, e a b → a < b := fun _ _ h => h.1.1
  have notGate (a b : Nat) (edge : e a b) (ne : b ≠ n) : neg b = false := by
    cases h : neg b
    · rfl
    · exact (ne (uniqueNot b edge.2 edge.1.2.1 h)).elim
  have liveShared : liveWire C shared := by
    obtain ⟨s, p⟩ := bin 1 (by decide)
    obtain ⟨_, edge⟩ := p.last_edge (by omega)
    exact edge.2
  have liveRoot : liveWire C C.output := ⟨true, .done⟩
  have rootGe : n ≤ C.output := by
    obtain ⟨_, p⟩ := liveN
    exact p.start_le (fun _ _ h => h.1)
  let onlyShared (a : Nat) := decide (a = shared)
  let both (a : Nat) := decide (a = shared ∨ a = n)
  let fShared := unfoldWithCuts C 6 (fun _ => false) shared
  let fBefore := unfoldWithCuts C 6 onlyShared n
  let fAfter := unfoldWithCuts C 6 both C.output
  have neg4 : SignedPath e neg C.output 4 false :=
    promised_signed_path C support realizes 2 4 false (by decide) (by decide) (by decide) (by decide)
  have neg5 : SignedPath e neg C.output 5 false :=
    promised_signed_path C support realizes 8 5 false (by decide) (by decide) (by decide) (by decide)
  have notOpposite {a : Nat} (avoid : ¬ reach a)
      (p : SignedPath e neg C.output a true) (q : SignedPath e neg C.output a false) : False :=
    avoid (p.reaches_unique_branch q forward unique)
  have avoidFromCut {cut : Nat → Bool} {w a : Nat} {s : Bool}
      (hc : cut shared = true) (away : a ≠ shared) (order : shared ≤ w)
      (path : SignedPath (liveCutEdge C cut) neg w a s) : ¬ reach a := by
    rintro ⟨t, toShared⟩
    exact toShared.no_enter_cut (path.map_edge (fun _ _ link =>
      ⟨link.1, fun eq => by simpa [eq, hc] using link.2⟩)) away forward order unique
  have ordinary {a : Nat} (small : a < 6) (hne : a ≠ 3) :
      a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 := by omega
  have useShared {a : Nat} {s : Bool} (h : fShared.hasPolarity a s) :
      s = true ∧ a < 6 ∧ a ≠ 3 ∧ reach a := by
    obtain ⟨allowed, p⟩ := trace_unfoldWithCuts C 6 (fun _ => false) shared a s support h
    have p := p.to_live_cut C (fun _ => false) liveShared
    have pt := p.map_edge (fun _ _ link => link.1)
    have sign := pt.positive_below forward (fun u v link bound => notGate u v link (by omega))
    exact ⟨sign, by simpa using allowed, fun eq => noThree (eq ▸ reachable_input_live C pt liveShared),
      _, pt⟩
  have useBefore {a : Nat} {s : Bool} (h : fBefore.hasPolarity a s) :
      s = false ∧ (a = shared ∨ (a < 6 ∧ a ≠ 3 ∧ ¬ reach a)) := by
    obtain ⟨allowed, raw⟩ := trace_unfoldWithCuts C 6 onlyShared n a s support h
    have p := raw.to_live_cut C onlyShared liveN
    have pt := p.map_edge (fun _ _ link => link.1)
    have smallOr : a < 6 ∨ a = shared := by simpa [onlyShared] using allowed
    have notN : a ≠ n := by rcases smallOr with h | h <;> omega
    refine ⟨pt.into_only_not notN negN notGate forward, ?_⟩
    by_cases aShared : a = shared
    · exact Or.inl aShared
    · exact Or.inr ⟨smallOr.resolve_right aShared,
        fun eq => noThree (eq ▸ reachable_input_live C pt liveN),
        avoidFromCut (by simp [onlyShared]) aShared (Nat.le_of_lt sharedLt) p⟩
  have useAfter {a : Nat} {s : Bool} (h : fAfter.hasPolarity a s) :
      s = true ∧ (a = shared ∨ a = n ∨ (a = 0 ∧ ¬ reach a)) := by
    obtain ⟨allowed, raw⟩ := trace_unfoldWithCuts C 6 both C.output a s support h
    have p := raw.to_live_cut C both liveRoot
    have pt := p.map_edge (fun _ _ link => link.1)
    have sign := p.all_positive (fun u v link => notGate u v link.1 (by
      intro eq
      subst v
      have cutFalse := link.2
      simp [both] at cutFalse))
    refine ⟨sign, ?_⟩
    have smallOr : a < 6 ∨ a = shared ∨ a = n := by simpa [both] using allowed
    by_cases aShared : a = shared
    · exact Or.inl aShared
    by_cases aNeg : a = n
    · exact Or.inr (Or.inl aNeg)
    have avoids := avoidFromCut (by simp [both]) aShared (by omega : shared ≤ C.output) p
    have small := smallOr.resolve_right (fun h => h.elim aShared aNeg)
    have aNot3 : a ≠ 3 := fun eq => noThree (eq ▸ reachable_input_live C pt liveRoot)
    rw [sign] at pt
    rcases ordinary small aNot3 with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨rfl, avoids⟩)
    · exact (avoids (bin 1 (by decide))).elim
    · exact (avoids (bin 2 (by decide))).elim
    · exact (notOpposite avoids pt neg4).elim
    · exact (notOpposite avoids pt neg5).elim
  let full (r a : Nat) := (C.wires (inputRow r)).getD a false
  let z (r : Nat) := full r shared
  let inv (r : Nat) := full r n
  let out (r : Nat) := full r C.output
  have zEval (r : Nat) : fShared.eval (full r) = z r :=
    eval_unfoldWithCuts C 6 (fun i => r.testBit i.val) (fun _ => false) shared support
  have invEval (r : Nat) : fBefore.eval (full r) = inv r :=
    eval_unfoldWithCuts C 6 (fun i => r.testBit i.val) onlyShared n support
  have outEval (r : Nat) : fAfter.eval (full r) = out r :=
    eval_unfoldWithCuts C 6 (fun i => r.testBit i.val) both C.output support
  have fit (r : Nat) (hr : r ∈ rows) : out r = target r :=
    eval_promised_row C realizes hr
  have zLe (r t : Nat)
      (raw : ∀ a, a < 6 → a ≠ 3 → reach a → r.testBit a ≤ t.testBit a) : z r ≤ z t := by
    rw [← zEval r, ← zEval t]
    apply Formula.eval_le_of_signed_le
    intro a s hp
    obtain ⟨rfl, small, ne, reaches⟩ := useShared hp
    simpa only [ite_true, full, input_value C r a small, input_value C t a small] using
      raw a small ne reaches
  have invLe (r t : Nat) (zs : z r ≤ z t)
      (raw : ∀ a, a < 6 → a ≠ 3 → ¬ reach a → r.testBit a = t.testBit a) :
      inv t ≤ inv r := by
    rw [← invEval r, ← invEval t]
    apply Formula.eval_le_of_signed_le
    intro a s hp
    obtain ⟨rfl, ha | ⟨small, ne, avoids⟩⟩ := useBefore hp
    · subst a
      exact zs
    · simp only [full, input_value C r a small, input_value C t a small]
      exact le_of_eq (raw a small ne avoids)
  have outLe (r t : Nat) (zs : z r ≤ z t) (ns : inv r ≤ inv t)
      (raw : r.testBit 0 = t.testBit 0) : out r ≤ out t := by
    rw [← outEval r, ← outEval t]
    apply Formula.eval_le_of_signed_le
    intro a s hp
    obtain ⟨rfl, ha | ha | ⟨ha, _⟩⟩ := useAfter hp
    · subst a
      exact zs
    · subst a
      exact ns
    · subst a
      simp only [ite_true, full, input_value C r 0 (by decide), input_value C t 0 (by decide)]
      exact le_of_eq raw
  have rawEq (r t : Nat)
      (h : r.testBit 0 = t.testBit 0 ∧ r.testBit 4 = t.testBit 4 ∧
        (¬ reach 5 → r.testBit 5 = t.testBit 5)) :
      ∀ a, a < 6 → a ≠ 3 → ¬ reach a → r.testBit a = t.testBit a := by
    intro a small ne avoids
    rcases ordinary small ne with rfl | rfl | rfl | rfl | rfl
    · exact h.1
    · exact (avoids (bin 1 (by decide))).elim
    · exact (avoids (bin 2 (by decide))).elim
    · exact h.2.1
    · exact h.2.2 avoids
  have outEq (r t : Nat) (zs : z r = z t)
      (raw : r.testBit 0 = t.testBit 0 ∧ r.testBit 4 = t.testBit 4 ∧
        (¬ reach 5 → r.testBit 5 = t.testBit 5)) : out r = out t := by
    have down := invLe r t (le_of_eq zs) (rawEq r t raw)
    have up := invLe t r (le_of_eq zs.symm)
      (fun a small ne avoids => (rawEq r t raw a small ne avoids).symm)
    exact le_antisymm (outLe r t (le_of_eq zs) up raw.1)
      (outLe t r (le_of_eq zs.symm) down raw.1.symm)
  have h8 : out 8 = true := fit 8 (by decide)
  have h18 : out 18 = false := fit 18 (by decide)
  have h32 : out 32 = false := fit 32 (by decide)
  have h34 : out 34 = true := fit 34 (by decide)
  have z8le32 := zLe 8 32 (fun a small ne _ => by
    rcases ordinary small ne with rfl | rfl | rfl | rfl | rfl <;> decide)
  have z32le34 := zLe 32 34 (fun a small ne _ => by
    rcases ordinary small ne with rfl | rfl | rfl | rfl | rfl <;> decide)
  have different32_34 : z 32 ≠ z 34 := by
    intro same
    have eq := outEq 32 34 same ⟨by decide, by decide, fun _ => by decide⟩
    simp [h32, h34] at eq
  have z32 : z 32 = false := by
    cases h : z 32
    · rfl
    · rw [h] at z32le34
      exact (different32_34 (h.trans (Bool.eq_true_of_true_le z32le34).symm)).elim
  have z34 : z 34 = true := by
    cases h : z 34
    · exact (different32_34 (z32.trans h.symm)).elim
    · rfl
  by_cases sharesFive : reach 5
  · have same : z 8 = z 32 := (Bool.eq_false_of_le_false (z32 ▸ z8le32)).trans z32.symm
    have eq := outEq 8 32 same ⟨by decide, by decide, fun avoids => (avoids sharesFive).elim⟩
    simp [h8, h32] at eq
  · have z8 : z 8 = false := Bool.eq_false_of_le_false (z32 ▸ z8le32)
    have z34le18 := zLe 34 18 (fun a small ne reaches => by
      rcases ordinary small ne with rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · exact (sharesFive reaches).elim)
    have z18 : z 18 = true := Bool.eq_true_of_true_le (z34 ▸ z34le18)
    have inv32 : inv 32 = false := by
      cases h : inv 32
      · rfl
      · have upper : inv 8 ≤ inv 32 := by rw [h]; exact Bool.le_true _
        have bad := outLe 8 32 (le_of_eq (z8.trans z32.symm)) upper (by decide)
        exact ((by decide : ¬ (true ≤ false)) (by simpa only [h8, h32] using bad)).elim
    have inv34 : inv 34 = true := by
      cases h : inv 34
      · have upper : inv 34 ≤ inv 18 := by rw [h]; exact Bool.false_le _
        have bad := outLe 34 18 (le_of_eq (z34.trans z18.symm)) upper (by decide)
        exact ((by decide : ¬ (true ≤ false)) (by simpa only [h34, h18] using bad)).elim
      · rfl
    have bad := invLe 32 34 z32le34 (rawEq 32 34 ⟨by decide, by decide, fun _ => by decide⟩)
    exact (by decide : ¬ (true ≤ false)) (by simpa only [inv32, inv34] using bad)

/-- The seven-gate upper-bound witness from the project desk. -/
def sevenGateWitness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [7]⟩,
    ⟨.and, [5, 8]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩

theorem seven_gates_suffice :
    ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧ realizesGraph C := by
  exact ⟨sevenGateWitness, by simp [sevenGateWitness, PEqualNP.MetaComplexity.FanInTwo],
    by decide, by unfold realizesGraph; decide +kernel⟩

end StructuralRefutation24221

