module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfNotFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def lprod {ι : Type} : List (Ex ι) → Ex ι
  | [] => Ex.one
  | a :: l => Ex.mul a (lprod l)

private theorem ev_lprod {ι : Type} (x : ι → ℂ) (l : List (Ex ι)) :
    (lprod l).ev x = (l.map (Ex.ev x)).prod := by
  induction l with
  | nil => simp [lprod, Ex.ev]
  | cons a l ih => simp [lprod, Ex.ev, ih]

private theorem exists_aff {ι : Type} (x y : ι → ℂ) (i : ι) (h : x i ≠ y i) :
    ∃ e : Ex ι, e.ev x = 1 ∧ e.ev y = 0 := by
  have hd : x i - y i ≠ 0 := sub_ne_zero.2 h
  refine ⟨Ex.smul (x i - y i)⁻¹ (Ex.add (Ex.gen i) (Ex.smul (-y i) Ex.one)), ?_, ?_⟩
  · simp only [Ex.ev]
    have : x i + -y i * 1 = x i - y i := by ring
    rw [this]
    exact inv_mul_cancel₀ hd
  · simp [Ex.ev]

private theorem sep_one (n : ℕ) (w : Pl E) {A A' : Multiset ℂˣ} (h : A.card = n) (h' : A'.card = n)
    (hne : A' ≠ A) : ∃ e : Ex (Fin (n + 1)), ev1 n w e A = 1 ∧ ev1 n w e A' = 0 := by
  have hex : ∃ j, j ≤ n ∧ satEig (qV E w) n A j ≠ satEig (qV E w) n A' j := by
    by_contra hc
    push_neg at hc
    exact hne (eq_of_satEig_eq (qV_ne_zero w) h h' hc).symm
  obtain ⟨j, hj, hj'⟩ := hex
  exact exists_aff (fun j : Fin (n + 1) => satEig (qV E w) n A j)
    (fun j : Fin (n + 1) => satEig (qV E w) n A' j) ⟨j, Nat.lt_succ_of_le hj⟩ hj'

private theorem sep_at (hP : Places) (n : ℕ) (S : Set (Pl E)) (hS : IsSection S) (Z : Finset (Pl E))
    (B C : Pl E → Multiset ℂˣ)
    (h : ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C w).card = n ∧ C w ≠ B w) :
    ∃ (t : Pl E) (e₁ e₂ : Ex (Fin (n + 1))), t ∈ S ∧ IsSplitAt t ∧ t ∉ Z ∧ ev1 n t e₁ (B t) = 1 ∧
      ev1 n t e₂ (inv (B (cPl t))) = 1 ∧ ev1 n t e₁ (C t) * ev1 n t e₂ (inv (C (cPl t))) = 0 := by
  obtain ⟨-, hc, -, hs⟩ := hP E
  obtain ⟨w, ⟨hwZ, hcZ⟩, hsp, hB, hC, hne⟩ := h
  rcases (hs S hS w).1 with hw | hw
  · obtain ⟨e, h1, h0⟩ := sep_one n w hB hC hne
    refine ⟨w, e, Ex.one, hw, hsp, hwZ, h1, ?_, ?_⟩
    · simp [ev1, Ex.ev]
    · rw [h0, zero_mul]
  · have hcc : cPl (cPl w) = w := (hc w).1
    have hsp' : IsSplitAt (cPl w) :=
      (hc (cPl w)).2.2 (by rw [hcc]; exact fun h => (hc w).2.1 hsp |>.elim h.symm)
    obtain ⟨e, h1, h0⟩ := sep_one n (cPl w) (A := inv (B w)) (A' := inv (C w))
      (by simpa [inv] using hB) (by simpa [inv] using hC)
      (fun h => hne (Multiset.map_injective inv_injective h))
    refine ⟨cPl w, Ex.one, e, hw, hsp', hcZ, by simp [ev1, Ex.ev], by rw [hcc]; exact h1, ?_⟩
    rw [hcc, h0, mul_zero]

private def comb {I : Type} [Fintype I] {n : ℕ} (t : I → Pl E) (e : I → Ex (Fin (n + 1))) (w : Pl E) :
    Ex (Fin (n + 1)) :=
  lprod ((Finset.univ : Finset I).toList.map fun j => if t j = w then e j else Ex.one)

private theorem evaluation_combined_test_function {I : Type} [Fintype I] {n : ℕ} (t : I → Pl E) (e : I → Ex (Fin (n + 1)))
    (w : Pl E) (X : Multiset ℂˣ) :
    ev1 n w (comb t e w) X = ∏ j, if t j = w then ev1 n w (e j) X else 1 := by
  rw [← Finset.prod_map_toList]
  simp only [ev1, comb]
  rw [ev_lprod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  by_cases hj : t j = w <;> simp [hj, Ex.ev]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.rSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RSep := by
  intro hP E _ _ _ n S hS Z I _ B C h
  haveI := Fintype.ofFinite I
  choose t e₁ e₂ htS hts htZ hB₁ hB₂ hC using fun j => sep_at hP n S hS Z B (C j) (h j)
  refine ⟨Finset.univ.image t, comb t e₁, comb t e₂, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨htS j, hts j⟩
  · refine Finset.disjoint_left.2 fun w hw hz => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact htZ j hz
  · refine Finset.prod_eq_one fun w _ => ?_
    rw [evaluation_combined_test_function, evaluation_combined_test_function]
    rw [show ∀ a b : ℂ, a = 1 → b = 1 → a * b = 1 from fun a b ha hb => by rw [ha, hb, one_mul]]
    · refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · subst hj
        exact hB₁ j
      · rfl
    · refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · subst hj
        exact hB₂ j
      · rfl
  · intro j
    refine Finset.prod_eq_zero (Finset.mem_image_of_mem t (Finset.mem_univ j)) ?_
    rw [evaluation_combined_test_function, evaluation_combined_test_function]
    rcases mul_eq_zero.1 (hC j) with h0 | h0
    · exact mul_eq_zero.2 (Or.inl (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))
    · exact mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

def cv {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ) : G → ℂ := fun y => hint K fun z => f z * g (z⁻¹ * y)

def cf (q a b j : ℕ) (p : Fin (a + 1) × Fin (b + 1)) : ℂ :=
  if (p.1 : ℕ) + p.2 = j then
    (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((b : ℂ) - (p.2 : ℕ)) + ((p.2 : ℕ) : ℂ) * ((a : ℂ) - (p.1 : ℕ))) / 2) else 0

def chi {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w) : ℂ :=
  (μ.loc w ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ)

def HintSph : Prop := ∀ (G : Type) [Group G] (K : Subgroup G) (u : G → ℂ), (∀ k ∈ K, ∀ x, u (x * k) = u x) → hint K u = ∑ᶠ q : G ⧸ K, u q.out

def CvHecke : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ f g : G → ℂ, IsHecke K f → IsHecke K g → IsHecke K (cv K f g)

def CvOp : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f g : G → ℂ), IsHecke K f → IsHecke K g →
  ∀ x ∈ fixed ρ K, levOp ρ K K (cv K f g) LinearMap.id x = levOp ρ K K f LinearMap.id (levOp ρ K K g LinearMap.id x) ∧
    levOp ρ K K g LinearMap.id x ∈ fixed ρ K ∧ levOp ρ K K g LinearMap.id x = heckeVec ρ K g x

def CtSph : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f : GLw n w → ℂ), IsHecke (KGL w (n := n)) f → ∀ m,
  ct h w f m = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
      ∑ᶠ q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w, f (blk h w m (Multiplicative.toAdd q.out)) ∧
    (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
      f (blk h w m (Multiplicative.toAdd q.out))).Finite

def CtLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f g : GLw n w → ℂ) (c : ℂ), IsHecke (KGL w (n := n)) f → IsHecke (KGL w (n := n)) g →
  ct h w (fun y => f y + g y) = (fun m => ct h w f m + ct h w g m) ∧ ct h w (fun y => c * f y) = fun m => c * ct h w f m

def CtUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n), ct h w ((KGL w (n := n) : Set _).indicator 1) = (K2 a b w : Set _).indicator 1

def CtT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (j : Fin (n + 1)) (m : GLw a w × GLw b w),
  ct h w (Tj ℂ n (Ov E w) (unif w) j) m = ∑ p : Fin (a + 1) × Fin (b + 1),
    cf (qV E w) a b j p * (Tj ℂ a (Ov E w) (unif w) p.1 m.1 * Tj ℂ b (Ov E w) (unif w) p.2 m.2)

def CtMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f g : GLw n w → ℂ), IsHecke (KGL w (n := n)) f → IsHecke (KGL w (n := n)) g →
  ct h w (cv (KGL w (n := n)) f g) = cv (K2 a b w) (ct h w f) (ct h w g)

def SatSum : Prop := ∀ (q a b : ℕ), q ≠ 0 → ∀ (B₁ B₂ : Multiset ℂˣ) (c₁ c₂ : ℂˣ), B₁.card = a → B₂.card = b → ∀ j : ℕ,
  satEig q (a + b) (B₁.map (· * c₁) + B₂.map (· * c₂)) j = ∑ p : Fin (a + 1) × Fin (b + 1),
    cf q a b j p * (c₁ : ℂ) ^ (p.1 : ℕ) * (c₂ : ℂ) ^ (p.2 : ℕ) * (satEig q a B₁ p.1 * satEig q b B₂ p.2)

def MuTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (μ : HChar E), μ.UnrAt w → ∀ (a b : ℕ),
  (∀ m ∈ K2 a b w, chi μ a b w m = 1) ∧ (∀ m m', chi μ a b w (m * m') = chi μ a b w m * chi μ a b w m') ∧
  ∀ (i j : ℕ) (m : GLw a w × GLw b w), i ≤ a → j ≤ b → Tj ℂ a (Ov E w) (unif w) i m.1 * Tj ℂ b (Ov E w) (unif w) j m.2 ≠ 0 →
    chi μ a b w m = ((μ.val w ^ b : ℂˣ) : ℂ) ^ i * ((μ.val w ^ a : ℂˣ) : ℂ) ^ j

def LevelU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → (∀ f : GLw n w → ℂ, Lc (KGL w (n := n)) f → Lc (KL n w) fun x : UL n w => f x.1) ∧
  ∀ f : GLw n w → ℂ, IsHecke (KGL w (n := n)) f → IsHecke (KL n w) fun x : UL n w => f x.1

def UnitHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E), IsOpen (KL n w : Set (UL n w)) ∧ IsHecke (KL n w) ((KL n w : Set _).indicator 1) ∧
  IsOpen (KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (KGL w (n := n) : Set (GLw n w)) ∧
  IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧
  ∀ k ∈ KGL w (n := n), thL n w k ∈ KGL w (n := n)

def TrUnit : Prop := ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G),
  twTr ρ K K ((K : Set G).indicator 1) LinearMap.id = (Module.finrank ℂ (fixed ρ K) : ℂ)

def TrSph : Prop := ExAct → SplitLine → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ), HasSatGL w τ.ρ B → ∀ e,
  twTr τ.ρ (KGL w (n := n)) (KGL w (n := n)) (fn1 n w e) LinearMap.id = ev1 n w e B

def UnramOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (π : Submodule ℂ (UA E n → ℂ)) (K' : ∀ w : Pl E, Subgroup (UL n w)), HasLevel S π K' →
  ∀ w ∈ S, K' w = KL n w → IsUnramU π w

def FinprodSplit : Prop := ∀ (α : Type) (S : Set α) (Z T : Finset α) (F : α → ℂ), (∀ w ∈ Z, w ∈ S) → (∀ w ∈ T, w ∈ S) → Disjoint T Z →
  (∀ w ∈ S, w ∉ Z → w ∉ T → F w = 1) → ∏ᶠ w ∈ S, F w = (∏ w ∈ Z, F w) * ∏ w ∈ T, F w

def DcosSep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
  Lc (KGL w (n := n)) (dcos n w (tdiag ϖ x)) ∧ ∀ y, dcos n w (tdiag ϖ x) y ≠ 0 → y.val.charpoly.Separable

def DcosTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (τ : SmIrr (GLw n w)),
  fixed τ.ρ (KGL w (n := n)) ≠ ⊥ → ∃ x : Fin n → ℤ, StrictAnti x ∧ trc τ.ρ (KGL w (n := n)) (dcos n w (tdiag ϖ x)) ≠ 0

def TrLevel : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) (K₁ K₂ : Subgroup G),
  IsOpen (K₂ : Set G) → K₂ ≤ K₁ → K₁ ≤ K → IsHecke K₁ f → FiniteDimensional ℂ (fixed ρ K₂) →
  twTr ρ K K₂ f LinearMap.id = twTr ρ K K₁ f LinearMap.id

def admitted : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
  FiniteDimensional ℂ (fixed τ.ρ U)

def RCtEx : Prop := ExAct → CtLin → CtUnit → CtT → CtMul → SatSum → MuTw → HintSph → CtEx

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_normal (K K₀ : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hK₀ : IsOpen (K₀ : Set G)) :
    ∃ N : Subgroup G, IsOpen (N : Set G) ∧ N ≤ K₀ ∧ N ≤ K ∧ (N.subgroupOf K).Normal := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set U := K₀.subgroupOf K with hU
  have hUo : IsOpen (U : Set K) := hK₀.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hUo
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUc : IsClosed (U : Set K) := U.isClosed_of_isOpen hUo
  have hcl : IsClosed (U.normalCore : Set K) := by
    have e : (U.normalCore : Set K) = ⋂ b : K, (fun a => b * a * b⁻¹) ⁻¹' (U : Set K) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [e]
    exact isClosed_iInter fun b => hUc.preimage (by fun_prop)
  have hco : IsOpen (U.normalCore : Set K) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  refine ⟨U.normalCore.map K.subtype, ?_, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ hco
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le U hx)
  · have e : (U.normalCore.map K.subtype).subgroupOf K = U.normalCore :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [e]
    exact Subgroup.normalCore_normal U

private theorem trc_eq {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K N : Subgroup G)
    (hKc : IsCompact (K : Set G)) (hNo : IsOpen (N : Set G)) (hNK : N ≤ K)
    (hfd : FiniteDimensional ℂ (fixed ρ N)) (F : G → ℂ) (hF : IsHecke N F) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.trc ρ K F = twTr ρ K N F LinearMap.id := by
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.trc
  refine (GlobalTheory.TraceLevel.twTr_level ρ K _ N F hNo hKc ?_ ?_ ⟨hF.1, ?_⟩ hfd).symm
  · intro k hk
    refine ⟨⟨hNK hk, fun x => (hF.2 k hk x).2⟩, fun x => ?_⟩
    show F (x * k)⁻¹ = F x⁻¹
    rw [_root_.mul_inv_rev, (hF.2 _ (N.inv_mem hk) _).1]
  · exact inf_le_left.trans inf_le_left
  · intro k hk x
    refine ⟨?_, hk.1.2 x⟩
    have h := hk.2 (x⁻¹ * k⁻¹)
    simp only [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h
    simpa using h.symm

end Gen

private theorem hint_sub {H : Type} [Group H] [Subsingleton H] (K : Subgroup H) (u : H → ℂ) : hint K u = u 1 := by
  unfold hint
  have h1 : (rStab u ⊓ K).relIndex K = 1 :=
    Subgroup.relIndex_eq_one.2 fun x _ => by
      rw [Subsingleton.elim x 1]
      exact one_mem _
  haveI : Unique (H ⧸ (rStab u ⊓ K)) :=
    { default := QuotientGroup.mk 1
      uniq := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => rw [Subsingleton.elim x 1] }
  have hu : ∀ x : H, u x = u 1 := fun x => by rw [Subsingleton.elim x 1]
  rw [h1, finsum_unique, hu]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem blk_zero {n : ℕ} (w : Pl E) (g : GLw n w) (m : GLw 0 w) (X : Matrix (Fin n) (Fin 0) (w.adicCompletion E)) :
    blk (Nat.add_zero n) w (g, m) X = g := by
  have e : ∀ i : Fin n, (finSumFinEquiv.trans (finCongr (Nat.add_zero n))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    ext
    simp
    rfl
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr (Nat.add_zero n))) (finSumFinEquiv.trans (finCongr (Nat.add_zero n)))
      (Matrix.fromBlocks g.val (g.val * X) 0 m.val) = g.val := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e, Matrix.fromBlocks_apply₁₁]
  have key : ∀ (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)), M = g.val →
      (if hM : IsUnit M then hM.unit else (1 : GLw n w)) = g := by
    rintro _ rfl
    rw [dite_eq_left g.isUnit]
    exact Units.ext rfl
  exact key _ hM

private theorem constant_term_parabolic_average {n : ℕ} (w : Pl E) (hw : IsSplitAt w) (μ : HChar E) (f : ∀ w : Pl E, GLw n w → ℂ) (g : GLw n w) :
    ct0 μ (Nat.add_zero n) f w (g, 1) = avg fun k : KGL w (n := n) => f w ((k : GLw n w)⁻¹ * g * k) := by
  haveI : Subsingleton (Multiplicative (Matrix (Fin n) (Fin 0) (w.adicCompletion E))) :=
    ⟨fun a b => Multiplicative.toAdd.injective (by ext i j; exact j.elim0)⟩
  have hU : ∀ y : GLw n w, y ∈ UL n w := fun y => by
    unfold UL
    rw [if_pos hw]
    trivial
  have hs : ∀ y : GLw n w, (toSub (UL n w) y : GLw n w) = y := fun y => by
    unfold toSub
    rw [dite_eq_left (hU y)]
  unfold ct0 ctMu ct
  rw [hint_sub]
  simp only [blk_zero, hs]
  have h0 : absHalf w ((g, (1 : GLw 0 w)).1.val.det ^ 0 / (g, (1 : GLw 0 w)).2.val.det ^ n) = 1 := by
    simp [absHalf, ordL]
    exact zpow_zero _
  rw [h0]
  simp

theorem trAvg : TrAvg := by
  intro E _ _ _ n w hw μ τ f hf
  obtain ⟨K₀, hK₀o, -, hH⟩ := hf
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  obtain ⟨N, hNo, hNK₀, hNK, hNn⟩ := exists_normal _ K₀ hKo hKc hK₀o
  have hfd := finiteDimensional_fixed_openSubgroup_GLw E n w τ N hNo
  have hfN : IsHecke N (f w) := ⟨hH.1, fun k hk x => hH.2 k (hNK₀ hk) x⟩
  obtain ⟨hFN, -, -, htr⟩ := GlobalTheory.ConjAvg.conjAvg E n w τ.V τ.ρ N hNo hNK hNn (f w) hfN
  have hct : (fun g => ct0 μ (Nat.add_zero n) f w (g, 1)) =
      fun g => avg fun k : KGL w (n := n) => f w ((k : GLw n w)⁻¹ * g * k) :=
    funext fun g => constant_term_parabolic_average w hw μ f g
  rw [hct, trc_eq τ.ρ _ N hKc hNo hNK hfd _ hFN, trc_eq τ.ρ _ N hKc hNo hNK hfd _ hfN, htr]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
section
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.inertLine :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.InertLine := by
  intro E _ _ _ hU n w _ σ hne hfd
  exact GlobalTheory.CompanionTheory.SphLine.sphOne E hU n w σ hne hfd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem eq_or_eq_cPl (w u : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w ∨ u = cPl w := by
  by_cases hs : IsSplitAt w
  · exact (GlobalTheory.SplitPts.over_split hs).2.2 u h
  · by_contra hc
    exact hs ⟨u, fun e => hc (Or.inl e), h⟩

private theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  let s : Setoid (Pl E) := Setoid.ker fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))
  refine ⟨Set.range fun q : Quotient s => q.out, fun w => ⟨(Quotient.mk s w).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact Quotient.mk_out (s := s) w
  · rintro u ⟨⟨q, rfl⟩, h⟩
    have hq : q = Quotient.mk s w := by
      conv_lhs => rw [← Quotient.out_eq q]
      exact Quotient.sound h
    rw [hq]

private theorem infinite_split : {w : Pl E | IsSplitAt w}.Infinite := by
  intro hfin
  obtain ⟨m, hm⟩ := (hfin.image fun w : Pl E => Ideal.absNorm w.asIdeal).bddAbove
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E m
  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQ]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w : Pl E := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rw [map_natCast]
    exact hpQ
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hsplit : IsSplitAt w := by
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩
  have hN : Ideal.absNorm w.asIdeal = p := (hs w.asIdeal w.isMaximal hpQ).1
  have hle : Ideal.absNorm w.asIdeal ≤ m := hm ⟨w, hsplit, rfl⟩
  omega

theorem places : Places := by
  intro E _ _ _
  refine ⟨exists_section, fun w => ?_, infinite_split, fun S hS w => ⟨?_, fun h₁ h₂ => ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := GlobalTheory.EulerTw.isSplitAt_iff_cPl_ne_and_cPl_cPl E w
    exact ⟨h₂, h₁⟩
  · obtain ⟨u, ⟨hu, hw⟩, -⟩ := hS w
    rcases eq_or_eq_cPl w u hw with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  · exact (hS w).unique ⟨h₂, GlobalTheory.LocInj.under_conjSrc w⟩ ⟨h₁, rfl⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
section
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regCt :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RegCt := by
  intro E _ _ _ w hw μ n a b h f hf
  exact GlobalTheory.BCT.CtReg.ctMu_regAt2 E a b n h w (μ.loc w) (fun x => f w x.1) hw (fun y => hf y.1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem small_tendsto {x : ℕ → ℂ} (h : Small (1 / 2) x) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨C, N, h⟩ := h
  refine squeeze_zero_norm h ?_
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N (r := (1 / 2 : ℝ)) (by norm_num [abs_of_pos])).comp
    (tendsto_add_atTop_nat 1)
  have h2 := h1.const_mul (C * 2)
  rw [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [add_comm (k : ℝ) 1]
  ring

theorem sat_card {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : CD E n} {w : Pl E} {B : Multiset ℂˣ}
    (h : D.Sat w B) : B.card = n := by
  obtain ⟨b, hb, rfl⟩ := h
  refine Eq.trans ?_ D.sum
  rw [Multiset.card_sum]
  exact Finset.sum_congr rfl fun i _ => (hb i).card

theorem off_cofinite {E : Type} [Field E] [NumberField E] [IsCMField E] (hP : Places) (Z : Finset (Pl E)) :
    ∀ᶠ w : Pl E in cofinite, Off Z w := by
  have h1 : ∀ᶠ w : Pl E in cofinite, w ∉ Z := Z.eventually_cofinite_notMem
  have h2 : ∀ᶠ w : Pl E in cofinite, w ∉ Z.image cPl := (Z.image cPl).eventually_cofinite_notMem
  filter_upwards [h1, h2] with w a b
  exact ⟨a, fun h => b (Finset.mem_image.2 ⟨_, h, ((hP E).2.1 w).1⟩)⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

