module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeSemicharacterVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.SemiCharValue

theorem exists_abstract_value {G R : Type} [AddCommGroup G] [AddCommGroup R] (ψ : AddChar R ℂ) (hψ : ∀ r, ‖ψ r‖ ≤ 1)
    (B : G → G → R) (hl : ∀ x y z, B (x + y) z = B x z + B y z) (hr : ∀ x y z, B x (y + z) = B x y + B x z)
    (ha : ∀ x, B x x = 0) (L : AddSubgroup G) (K : G → Prop) (K0 : K 0) (Ksub : ∀ x y, K x → K y → K (x - y))
    (hKL : ∀ l ∈ L, K l → l = 0) (hB : ∀ x, K x → ∀ l ∈ L, B x l = 0)
    (h2 : ∀ a ∈ L, ∀ u ∈ L, ψ (B a u + B a u) = 1)
    (p q : G → G) (padd : ∀ x y, p (x + y) = p x + p y) (pq : ∀ x, p x + q x = x)
    (adj : ∀ x y, B (p x) y = B x (q y)) (pL : ∀ l ∈ L, p l ∈ L) :
    ∃ χ : G → ℂ, (∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧
      (∀ x y, K y → χ (x + y) = χ x) ∧ (∀ u ∈ L, ∀ x, ψ (B x (2 • u)) * χ (x + 2 • u) = χ x) ∧
      (∀ u ∈ L, B (p u) u = 0 → ∀ x, ψ (B x u) * χ (x + u) = χ x) ∧
      ∀ l ∈ L, χ l = ψ (B (p l) l) := by
  classical
  have Kadd : ∀ x y, K x → K y → K (x + y) := fun x y hx hy => by
    have := Ksub x (0 - y) hx (Ksub 0 y K0 hy)
    rwa [zero_sub, sub_neg_eq_add] at this
  have skew : ∀ x y, B x y + B y x = 0 := fun x y => by
    have := ha (x + y)
    rwa [hl, hr, hr, ha, ha, zero_add, add_zero] at this
  let χ : G → ℂ := fun x => if h : ∃ l ∈ L, K (x - l) then ψ (B (p h.choose) h.choose) else 0
  have hn : ∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0 := fun x h => dif_neg h
  have hy : ∀ x, ∀ l ∈ L, K (x - l) → χ x = ψ (B (p l) l) := fun x l hl' hk => by
    have h : ∃ l ∈ L, K (x - l) := ⟨l, hl', hk⟩
    have e : h.choose = l := by
      have h1 := Ksub _ _ hk h.choose_spec.2
      rw [sub_sub_sub_cancel_left] at h1
      exact sub_eq_zero.1 (hKL _ (L.sub_mem h.choose_spec.1 hl') h1)
    show dite _ _ _ = _
    rw [dite_eq_left h, e]
  have gen : ∀ u ∈ L, (∀ l ∈ L, ψ (B l u) * ψ (B (p (l + u)) (l + u)) = ψ (B (p l) l)) →
      ∀ x, ψ (B x u) * χ (x + u) = χ x := fun u hu H x => by
    by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      have e : B x u = B l u := by
        have := hl (x - l) l u
        rwa [sub_add_cancel, hB _ hk u hu, zero_add] at this
      rw [hy x l hl' hk, hy (x + u) (l + u) (L.add_mem hl' hu) (by rwa [add_sub_add_right_eq_sub]), e, H l hl']
    · rw [hn x h, hn (x + u), mul_zero]
      rintro ⟨l, hl', hk⟩
      exact h ⟨l - u, L.sub_mem hl' hu, by rwa [← sub_add, sub_add_eq_add_sub]⟩
  refine ⟨χ, hn, fun x => ?_, ?_, fun x y hk => ?_, fun u hu => ?_, fun u hu h0 => ?_,
    fun l hl' => hy l l hl' (by rwa [sub_self])⟩
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk]; exact hψ _
    · rw [hn x h]; simp
  · rw [hy 0 0 L.zero_mem (by rwa [sub_zero])]
    have : B (p 0) 0 = 0 := by
      have := hr (p 0) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [this, AddChar.map_zero_eq_one]
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk, hy (x + y) l hl' (by rw [← sub_add_eq_add_sub]; exact Kadd _ _ hk ‹_›)]
    · rw [hn x h, hn (x + y)]
      rintro ⟨l, hl', hk'⟩
      refine h ⟨l, hl', ?_⟩
      have := Ksub _ _ hk' hk
      rwa [show x + y - l - y = x - l by abel] at this
  · refine gen _ (L.nsmul_mem hu 2) fun l hl' => ?_
    have e : B (p (l + 2 • u)) (l + 2 • u) = B (p l) l + (B (p l) u + B (p l) u) +
        (B (p u) (l + 2 • u) + B (p u) (l + 2 • u)) := by
      conv_lhs => rw [padd, hl, hr, two_nsmul, hr, padd, hl]
      rw [two_nsmul]
    rw [e, two_nsmul, hr, h2 l hl' u hu, one_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      h2 _ (pL l hl') u hu, h2 _ (pL u hu) _ (L.add_mem hl' (L.add_mem hu hu)), mul_one, mul_one]
  · refine gen _ hu fun l hl' => ?_
    have e : B l u + B (p (l + u)) (l + u) = B (p l) l + (B (p l) u + B (p l) u) := by
      have e1 : B l u = B (p l) u + B (q l) u := by rw [← hl, pq]
      have e2 := skew u (q l)
      rw [padd, hl, hr, hr, h0, adj u l, e1]
      rw [← sub_eq_zero]
      refine Eq.trans ?_ e2
      abel
    rw [← AddChar.map_add_eq_mul, e, AddChar.map_add_eq_mul, h2 _ (pL l hl') u hu, mul_one]

theorem exists_semichar_value : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ b : 𝓞 D.host.E, (b : D.host.E) + star (b : D.host.E) = 1 → ∃ χ : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) χ ∧ ∀ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), χ l = ψ (symplOH S T (l.map fun z => incA D (b : D.host.E) * z) l) := by
  intro D ψ S T ΛS ΛT hψ hS hT b hb
  have hinf := GlobalTheory.SemiChar.latO_inf S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True
  obtain ⟨f1, f2, f3, f4, -, -, f7, f8, f9⟩ := _root_.GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have g := (_root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨χ, -, -, -, -, c5, c6, c7⟩ := exists_abstract_value ψ (fun r => (hψ.1.2.1 r).le) (symplOH S T) f1 f2 f3
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (fun x => x.map (finPart D) = 0) (by funext i j; exact (finPart D).map_zero)
    (fun x y hx hy => by
      funext i j
      have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
      have h2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
      show finPart D (x i j - y i j) = 0
      rw [RingHom.map_sub, h1, h2, sub_zero])
    (fun l hl hk => by
      funext i j
      exact GlobalTheory.FockCompare.RealChart.adele_tensor_ext (l i j) (congrFun (congrFun (hinf l hl) i) j)
        (congrFun (congrFun hk i) j))
    (fun x hx l hl => f9 x l hx (hinf l hl))
    (fun a ha u hu => by rw [f4]; exact (g a (hinf a ha)).1 ha u hu)
    (fun x => x.map fun z => incA D (b : D.host.E) * z) (fun x => x.map fun z => cA D (incA D (b : D.host.E)) * z)
    (GlobalTheory.SemiChar.map_mul_add _)
    (fun x => by
      funext i j
      show incA D (b : D.host.E) * x i j + incA D (star (b : D.host.E)) * x i j = x i j
      rw [← add_mul, ← RingHom.map_add (f := _), hb, RingHom.map_one, one_mul])
    (f7 _) (GlobalTheory.SemiChar.latO_mul_int S T _ _ _ b)
  refine ⟨χ, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, c7⟩
  · funext x; exact c5 u hu x
  · funext x; exact c6 u hu (f8 e _ u he.2.1 hh) x

end GlobalTheory.SemiCharValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneCompl

theorem gram_sum {D : D7} (S : HSp D) (a b : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (a i) * S.gram i j * b j = S.hT (S.frame.equivFun.symm a) (S.frame.equivFun.symm b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_compl : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  intro D S Λ x y s hΛ hxx hyy hxy hsplit
  have hyx : S.hT y x = 1 := by rw [← S.herm.eq x y, hxy, map_one]
  let W : Submodule D.host.E S.V := LinearMap.ker (LinearMap.pi fun j : Fin 2 => S.hT (![x, y] j))
  have hW : ∀ w, w ∈ W ↔ S.hT x w = 0 ∧ S.hT y w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply, Matrix.head_cons]
  have hdec : ∀ z, z - S.hT y z • x - S.hT x z • y ∈ W := by
    intro z
    rw [hW]
    constructor <;> simp [map_sub, hxx, hyy, hxy, hyx]
  have hind : LinearIndependent D.host.E ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (S.hT x) hab
    have h2 := congrArg (S.hT y) hab
    simp [hxx, hyy, hxy, hyx] at h1 h2
    exact ⟨h2, h1⟩
  have hrk : 2 + Module.finrank D.host.E W = S.rank := by
    have := GlobalTheory.WittLow.finrank_orth S.herm S.nondeg ![x, y] hind
    rw [S.rank_eq] at this
    exact this

  have hrad : ∀ v : W, (∀ w : W, S.hT w v = 0) → v = 0 := by
    intro v hv
    have hv' := (hW v).1 v.2
    apply Subtype.ext
    apply S.nondeg.2 (v : S.V)
    intro z
    have e : z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y := by abel
    have h0 := hv ⟨_, hdec z⟩
    rw [e, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.smul_apply, hv'.1, hv'.2, h0]
    simp
  let h' : W →ₗ⋆[D.host.E] W →ₗ[D.host.E] D.host.E := S.hT.domRestrict₁₂ W W
  have hs' : h'.IsSymm := ⟨fun a b => S.herm.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun a ha => hrad a fun b => by
    rw [← S.herm.eq]; exact (congrArg _ (ha b)).trans (map_zero _), fun a ha => hrad a ha⟩
  let Λ' : Submodule (𝓞 D.host.E) S.V := Λ.comap ((S.frame.equivFun : S.V →ₗ[D.host.E] (Fin S.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hΛ'm : ∀ z, z ∈ Λ' ↔ GlobalTheory.SqStepK.InLat S Λ z := fun z => Iff.rfl
  have hΛ'lat : Submodule.IsLattice D.host.E Λ' := GlobalTheory.ColRows.isLattice_comap_equiv S.frame.equivFun Λ hΛ.1
  have hΛ'd : ∀ z, z ∈ Λ' ↔ ∀ w ∈ Λ', ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT w z := by
    intro z
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, hΛ.2]
    constructor
    · intro h w hw
      obtain ⟨b, hb⟩ := h _ hw
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
    · intro h a ha
      obtain ⟨b, hb⟩ := h (S.frame.equivFun.symm a) (by rw [hΛ'm, GlobalTheory.SqStepK.InLat, LinearEquiv.apply_symm_apply]; exact ha)
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
  let L0 : Submodule (𝓞 D.host.E) W := Λ'.comap (W.subtype.restrictScalars (𝓞 D.host.E))
  have hL0m : ∀ u : W, u ∈ L0 ↔ (u : S.V) ∈ Λ' := fun u => Iff.rfl
  have hL0lat : Submodule.IsLattice D.host.E L0 := GlobalTheory.isLattice_comap_subtype_ringOfIntegers Λ' hΛ'lat W
  have hwz : ∀ z, z ∈ Λ' → z - S.hT y z • x - S.hT x z • y ∈ Λ' := by
    intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z ((hΛ'm z).1 hz)
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, map_sub, map_sub]
    exact Λ.sub_mem (Λ.sub_mem hz hs1) hr1
  have hL0d : ∀ u : W, u ∈ L0 ↔ ∀ u' ∈ L0, ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT u' u := by
    intro u
    have hu := (hW u).1 u.2
    rw [hL0m, hΛ'd]
    constructor
    · intro h u' hu'
      exact h _ hu'
    · intro h z hz
      obtain ⟨b, hb⟩ := h ⟨_, hdec z⟩ (hwz z hz)
      refine ⟨b, ?_⟩
      rw [hb]
      simp [map_sub, hu.1, hu.2]
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L0 := by
    ext v
    rw [GlobalTheory.WittLow.mem_dual, hL0d]
    refine forall₂_congr fun u' _ => ?_
    rw [Submodule.mem_one]
    rfl

  let S₁ : HSp D :=
    { V := W, hT := h', herm := hs', nondeg := hnd', rank := Module.finrank D.host.E W, rank_eq := rfl,
      frame := Module.finBasis D.host.E W, sig := s, L0 := L0, standardTuple_isLattice := hL0lat, baseLattice_isUnimodular := hun }
  let e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) ≃ₗ[D.host.E] W := (Module.finBasis D.host.E W).equivFun.symm
  let Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E) :=
    L0.comap ((e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) →ₗ[D.host.E] W).restrictScalars (𝓞 D.host.E))
  have hΛ₁m : ∀ v, v ∈ Λ₁ ↔ e₁ v ∈ L0 := fun v => Iff.rfl
  have hΛ₁lat : Submodule.IsLattice D.host.E Λ₁ := GlobalTheory.ColRows.isLattice_comap_equiv e₁ L0 hL0lat
  have hin : ∀ u : W, GlobalTheory.SqStepK.InLat S₁ Λ₁ u ↔ GlobalTheory.SqStepK.InLat S Λ (W.subtype u) := by
    intro u
    change (Module.finBasis D.host.E W).equivFun u ∈ Λ₁ ↔ _
    rw [hΛ₁m]
    change (Module.finBasis D.host.E W).equivFun.symm ((Module.finBasis D.host.E W).equivFun u) ∈ L0 ↔ _
    rw [LinearEquiv.symm_apply_apply, hL0m, hΛ'm]
    rfl
  refine ⟨S₁, Λ₁, W.subtype, ⟨?_, fun _ _ => rfl, hxx, hyy, hyx, fun u => ⟨((hW u).1 u.2).1, ((hW u).1 u.2).2⟩, hin, ?_⟩, ⟨hΛ₁lat, ?_⟩, rfl⟩
  · change S.rank = Module.finrank D.host.E W + 2
    omega
  · intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z hz
    refine ⟨S.hT y z, S.hT x z, ⟨_, hdec z⟩, hs1, hr1, (hin _).2 (hwz z hz), ?_⟩
    change z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y
    abel
  · intro v
    simp only [gram_sum]
    rw [hΛ₁m, hL0d]
    constructor
    · intro h a ha
      exact h _ ha
    · intro h u' hu'
      have := h (e₁.symm u') (by rw [hΛ₁m, LinearEquiv.apply_symm_apply]; exact hu')
      obtain ⟨b, hb⟩ := this
      refine ⟨b, ?_⟩
      rw [hb]
      change S.hT (e₁ (e₁.symm u') : S.V) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory.PlaneCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport.Onto

open scoped TensorProduct

theorem swapAE_sigR (D : D7) (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    Lev.swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Lev.swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]
  | tmul a e => rfl

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.sgA D y)) = _
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  exact swapAE_sigR D _

def adSwapEquiv (D : D7) : StandardLatticesGL3.AE D ≃+* Lev.EAf D :=
  (GlobalTheory.BotFormula.toAfE D).trans (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem adSwapEquiv_apply (D : D7) (y : StandardLatticesGL3.AE D) : adSwapEquiv D y = adSwap D y := rfl

theorem sigR_inclEAf (D : D7) (e : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D e) = inclEAf D (D.sp.cm.sig e) := rfl

end GlobalTheory.FrameTransport.Onto

namespace GlobalTheory.FrameTransport.Onto

theorem cT_map_inclEAf (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) :
    (Formalism.UG.cT (↑D.sp.cm.sig) A).map (inclEAf D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (inclEAf D)) := by
  ext i j
  exact (sigR_inclEAf D (A j i)).symm

theorem cT_map_adSwap (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) :
    (Formalism.UG.cT (StandardLatticesGL3.sgA D) A).map (adSwap D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (adSwap D)) := by
  ext i j
  exact adSwap_sgA D (A j i)

theorem conj_unitary {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J P Pi M : Matrix (Fin n) (Fin n) R)
    (hPPi : P * Pi = 1) (hP : Formalism.UG.cT s P * J * P = 1) (hM : Formalism.UG.cT s M * J * M = J) :
    Formalism.UG.cT s (Pi * M * P) * (Pi * M * P) = 1 := by
  have h2 : Formalism.UG.cT s Pi * Formalism.UG.cT s P = 1 := by rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hJ : J = Formalism.UG.cT s Pi * Pi := by
    calc J = (Formalism.UG.cT s Pi * Formalism.UG.cT s P) * J * (P * Pi) := by rw [h2, hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Pi * (Formalism.UG.cT s P * J * P) * Pi := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ← hP]
  calc _ = Formalism.UG.cT s P * (Formalism.UG.cT s M * (Formalism.UG.cT s Pi * Pi) * M) * P := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hJ, hM]

theorem _root_.GlobalTheory.FrameTransport.exists_frConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  intro D V fr hfr M hM
  let P : GL (Fin V.rank) (Lev.EAf D) := Formalism.UG.bc (inclEAf D) fr
  let N : GL (Fin V.rank) (Lev.EAf D) := P⁻¹ * M * P
  let h0 : GL (Fin V.rank) (StandardLatticesGL3.AE D) := Formalism.UG.bc (adSwapEquiv D).symm.toRingHom N
  have hbc : Formalism.UG.bc (adSwap D) h0 = N := by
    ext i j
    show adSwap D ((adSwapEquiv D).symm _) = _
    rw [← adSwapEquiv_apply, RingEquiv.apply_symm_apply]
  have hbcm : h0.val.map (adSwap D) = N.val := congrArg Units.val hbc
  have hPPi : P.val * (P⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) P.val * V.gram.map (inclEAf D) * P.val = 1 := by
    have := congrArg (fun X => X.map (inclEAf D)) hfr
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_map_inclEAf] at this
    exact this
  have hN : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) N.val * N.val = 1 := by
    have hNv : N.val = (P⁻¹).val * M.val * P.val := by simp only [N, Units.val_mul]
    rw [hNv]
    exact conj_unitary _ _ _ _ _ hPPi hfr' hM
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · show Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) *
        h0.val = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    apply Matrix.map_injective (adSwapEquiv D).injective
    change (Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val * h0.val).map (adSwap D) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (adSwap D)
    rw [Matrix.map_mul, cT_map_adSwap, hbcm, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  · show frConj fr h0 = M
    rw [frConj_apply, hbc]
    show P * (P⁻¹ * M * P) * P⁻¹ = M
    group

end GlobalTheory.FrameTransport.Onto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhE
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameTransport.IntSwap

theorem toFinE_mem_intAd {D : D7} {x : StandardLatticesGL3.AE D} (hx : x ∈ StandardLatticesGL3.OhE D) :
    GlobalTheory.BotFormula.toFinE D x ∈ Formalism.UG.intAd D.host.E := by
  have key : ∀ y : StandardLatticesGL3.AE D,
      (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)) y ∈
        AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ℚ ⊗[ℚ] D.host.E |
          ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf ℚ, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[ℚ] (o : D.host.E)} →
      GlobalTheory.BotFormula.toFinE D y ∈ Formalism.UG.intAd D.host.E := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).1 hy
  have hle : StandardLatticesGL3.OhE D ≤ (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      refine key _ (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, rfl⟩)
      exact (one_mem (v.adicCompletionIntegers ℚ) : _)
    · refine key _ (AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, ?_⟩)
      rfl
  exact hle hx

theorem swapAE_mem_intAf {D : D7} {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)}) :
    Lev.swapAE D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hle : AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} ≤
      (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup.comap (Lev.swapAE D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, o, rfl⟩
    have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        ((o : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) *
          ((1 : D.host.E) ⊗ₜ[D.host.F] (a : Formalism.L2.Herm.Af D.host.F)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    show Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
    rw [e]
    refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨(o : D.host.E), o, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
  exact hle hy

end GlobalTheory.FrameTransport.IntSwap

theorem GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D →
    GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D x hx
  have h1 := GlobalTheory.FrameTransport.IntSwap.toFinE_mem_intAd hx
  have h2 : GlobalTheory.BotFormula.toAfE D x ∈ AddSubgroup.closure
      {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
        ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} := by
    refine (GlobalTheory.LFun.mem_int_iff _).2 fun P => ?_
    have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.BotFormula.toAfE D x) = GlobalTheory.BotFormula.toFinE D x :=
      (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _
    rw [e]
    exact h1 P
  exact GlobalTheory.FrameTransport.IntSwap.swapAE_mem_intAf h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducibleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  first | exact @GlobalTheory.MinorFrame.RowIrr.inv_irreducible | exact GlobalTheory.MinorFrame.RowIrr.inv_irreducible | (intros; apply GlobalTheory.MinorFrame.RowIrr.inv_irreducible <;> assumption)
end

