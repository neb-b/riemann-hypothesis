module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergEpsilonTransport
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairEpsTransport

section Maps
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_longElt (n : ℕ) : GeneralLinearGroup.map f (longElt n R) = longElt n S := by
  ext i j; simp [longElt, GeneralLinearGroup.map]

theorem map_invT (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (GlobalTheory.CuspRep.invT n R g) = GlobalTheory.CuspRep.invT n S (GeneralLinearGroup.map f g) := by
  ext i j
  have h := congrArg (fun h : GL (Fin n) S => (h : Matrix (Fin n) (Fin n) S) j i)
    (map_inv (GeneralLinearGroup.map f) g)
  exact h

theorem map_tilde {n : ℕ} (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (tilde g) = tilde (GeneralLinearGroup.map f g) := by
  rw [tilde, tilde, map_mul, map_longElt, map_invT]

theorem map_corner {m : ℕ} (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (corner g) = corner (GeneralLinearGroup.map f g) := by
  ext i j
  show f ((emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1) : Matrix _ _ R) i j) =
    (emb₂ S (stdSum (rfl : m + 1 = m + 1)) (GeneralLinearGroup.map f g, 1) : Matrix _ _ S) i j
  rw [val_emb₂, val_emb₂]
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, GeneralLinearGroup.map] <;> split_ifs <;> simp

theorem superDiag_map {n : ℕ} (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map f g) = f (GlobalTheory.Whittaker.superDiag g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.Whittaker.superDiag, map_sum, GeneralLinearGroup.map]

theorem map_mem_unipB {n : ℕ} {g : GL (Fin n) R} (hg : g ∈ unipB R (Fin n)) :
    GeneralLinearGroup.map f g ∈ unipB S (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [GeneralLinearGroup.map, hg.1 i j h]
  · simp [GeneralLinearGroup.map, hg.2 i]

end Maps

section Core

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

theorem map_map_symm {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

theorem map_symm_map {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k) :
    GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

theorem continuous_mapGL {n : ℕ} (i : k ≃+* k') (hi : Continuous i) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hi
  · exact Units.continuous_coe_inv.matrix_map hi

end Core

section Transport

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

theorem isTestFun_comp {m : ℕ} (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {f : GL (Fin m) k → ℂ} (hf : IsTestFun f) :
    IsTestFun (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g)) := by
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  refine ⟨fun u hu g => ?_, h2.comp_continuous (continuous_mapGL i.symm hi'), ?_⟩
  · show f (GeneralLinearGroup.map i.symm.toRingHom (u * g)) = f (GeneralLinearGroup.map i.symm.toRingHom g)
    rw [map_mul]
    exact h1 _ (map_mem_unipB _ hu) _
  · refine ⟨GeneralLinearGroup.map i.toRingHom '' C, hC.image (continuous_mapGL i hi), fun g hg => ?_⟩
    obtain ⟨u, hu, c, hc, he⟩ := h3 _ hg
    refine ⟨GeneralLinearGroup.map i.toRingHom u, map_mem_unipB _ hu, GeneralLinearGroup.map i.toRingHom c,
      ⟨c, hc, rfl⟩, ?_⟩
    rw [← map_mul, ← he, map_map_symm]

variable {m : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem hasPairEps_of_equiv (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {ψ : AddChar k Circle} {ψ' : AddChar k' Circle} (hψ : ∀ x, ψ' (i x) = ψ x)
    {π : Representation ℂ (GL (Fin (m + 1)) k) V} {π' : Representation ℂ (GL (Fin (m + 1)) k') V'}
    {τ : Representation ℂ (GL (Fin m) k) W} {τ' : Representation ℂ (GL (Fin m) k') W'}
    (A : V ≃ₗ[ℂ] V') (hA : ∀ g v, A (π g v) = π' (GeneralLinearGroup.map i.toRingHom g) (A v))
    (B : W ≃ₗ[ℂ] W') (hB : ∀ g v, B (τ g v) = τ' (GeneralLinearGroup.map i.toRingHom g) (B v))
    {c : ℂ} (H : HasPairEps ψ π τ c) : HasPairEps ψ' π' τ' c := by
  intro ω' hω' l' L' hl' hL' I' hI' v' w'
  have hψinv : ∀ x, (ψ'⁻¹) (i x) = (ψ⁻¹) x := by
    intro x; simp only [AddChar.inv_apply]; rw [← map_neg, hψ]
  have hω : HasCentralChar τ (ω'.comp (Units.map i.toRingHom.toMonoidHom)) := by
    intro z w
    apply B.injective
    rw [hB, GeneralLinearGroup.map_scalar, hω', map_smul]
    rfl
  have hl : GlobalTheory.Whittaker.IsFunctional ψ π (l'.comp A.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hA, hl' _ (map_mem_unipB _ hu), superDiag_map]
    simp [hψ]
  have hL : GlobalTheory.Whittaker.IsFunctional ψ⁻¹ τ (L'.comp B.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hB, hL' _ (map_mem_unipB _ hu), superDiag_map]
    have := hψinv (GlobalTheory.Whittaker.superDiag u)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
  have hI : IsInvIntegral (I'.comp (LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom))) := by
    intro f hf x
    change I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g * x)) =
      I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g))
    have := hI' _ (isTestFun_comp i hi hi' hf) (GeneralLinearGroup.map i.toRingHom x)
    refine Eq.trans ?_ this
    congr 1
    funext g
    rw [map_mul, map_symm_map]
  have key := H _ hω _ _ hl hL _ hI (A.symm v') (B.symm w')
  have e1 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (tilde (corner g)) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ (tilde g) (B.symm w'))) =
      fun g => l' (π' (tilde (corner g)) v') * L' (τ' (tilde g) w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_tilde, map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e2 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (corner g) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ g (B.symm w'))) =
      fun g => l' (π' (corner g) v') * L' (τ' g w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e3 : (ω'.comp (Units.map i.toRingHom.toMonoidHom)) (-1) = ω' (-1) := by
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3] at key
  exact key
end Transport

section Main

theorem equiv_apply_rep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) v

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem exists_equiv_of_repRel (i : k ≃+* k') {n : ℕ} {π : IrrRep (GL (Fin n) k)} {π' : IrrRep (GL (Fin n) k')}
    (h : RepRel i (cls π) (cls π')) :
    ∃ E : π.V ≃ₗ[ℂ] π'.V, ∀ g v, E (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (E v) := by
  obtain ⟨n₀, π₀, π₀', e, h1, h2, he⟩ := h
  obtain ⟨rfl, h1⟩ := Sigma.mk.inj_iff.1 h1
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h2
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h1)
  obtain ⟨φ'⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h2)
  refine ⟨φ.toLinearEquiv ≪≫ₗ e ≪≫ₗ φ'.toLinearEquiv.symm, fun g v => ?_⟩
  apply φ'.toLinearEquiv.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [equiv_apply_rep φ, he, equiv_apply_rep φ', LinearEquiv.apply_symm_apply]

end Main

end GlobalTheory.PairEpsTransport


open GlobalTheory.PairEpsTransport in
theorem GlobalTheory.LocLanglands.hasPairEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' hψ m π π' τ τ' c hπ hτ H
  have hi' : Continuous i.symm := (_root_.GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation k k' i hi).1
  obtain ⟨A, hA⟩ := exists_equiv_of_repRel i hπ
  obtain ⟨B, hB⟩ := exists_equiv_of_repRel i hτ
  exact hasPairEps_of_equiv i hi hi' hψ A hA B hB H

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransport
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

theorem isTateEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' χ χ' e hψ hχ he
  classical
  obtain ⟨_, hv1, hord, hres, _⟩ := continuous_iso_keeps_valuation k k' i hi
  set u : kˣ →* k'ˣ := Units.map i.toRingHom.toMonoidHom with hu
  have hcoe : ∀ x : kˣ, ((u x : k'ˣ) : k') = i x := fun x => rfl
  have hle : ∀ x y : k, valuation k' (i x) ≤ valuation k' (i y) ↔ valuation k x ≤ valuation k y := by
    intro x y
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy' : i y ≠ 0 := by simpa using hy
      have h1 := hv1 (x / y)
      rw [map_div₀, map_div₀, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hy'),
        div_le_one₀ ((Valuation.pos_iff _).2 hy)] at h1
      exact h1
  have hsurj : ∀ x' : k'ˣ, ∃ x : kˣ, u x = x' := fun x' =>
    ⟨Units.map i.symm.toRingHom.toMonoidHom x', by ext; simp [hu]⟩
  have huinj : Function.Injective u := fun x y h => by
    ext; exact i.injective (by simpa [hcoe] using congrArg (fun z : k'ˣ => (z : k')) h)
  have hunif : ∀ a : ℕ, ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧
      valuation k' (i p) = uniformizer k' ^ a := by
    intro a
    obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
    obtain ⟨q, hq, hq'⟩ := exists_unit_pow k' a
    refine ⟨p, hp, ?_⟩
    rw [← hq, ← hcoe, valuation_eq_iff_ord, hord, hp', hq']
  have hfilt : ∀ (x : kˣ) (b : ℕ), u x ∈ unitFilt k' b ↔ x ∈ unitFilt k b := by
    intro x b
    obtain ⟨p, hp, hp'⟩ := hunif b
    simp only [unitFilt, Set.mem_setOf_eq]
    have e1 : valuation k' ((u x : k'ˣ) : k') = 1 ↔ valuation k (x : k) = 1 := by
      rw [← ord_eq_zero_iff, ← ord_eq_zero_iff, hord]
    have e2 : valuation k' (((u x : k'ˣ) : k') - 1) ≤ uniformizer k' ^ b ↔
        valuation k ((x : k) - 1) ≤ uniformizer k ^ b := by
      have hs : i ((x : k) - 1) = i x - 1 := by rw [map_sub, map_one]
      rw [← hp, ← hp', hcoe, ← hle, hs]
    rw [e1, e2]
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := he
  refine ⟨u c, a, R.image u, ?_, ?_, ?_, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := i.surjective x'
    rw [hcoe, hle, ← hc x]
    constructor
    · intro h y hy
      rw [← hψ]
      exact h (i y) ((hle y x).2 hy)
    · intro h y' hy'
      obtain ⟨y, rfl⟩ := i.surjective y'
      rw [hψ]
      exact h y ((hle y x).1 hy')
  · refine ⟨fun x' hx' => ?_, fun b hb => ?_⟩
    · obtain ⟨x, rfl⟩ := hsurj x'
      rw [hχ]
      exact ha.1 x ((hfilt x a).1 hx')
    · obtain ⟨x, hx, hx'⟩ := ha.2 b hb
      exact ⟨u x, (hfilt x b).2 hx, by rw [hχ]; exact hx'⟩
  · refine ⟨fun r' hr' => ?_, fun y' hy' => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr'
      rw [hord, hord]
      exact hR.1 r hr
    · obtain ⟨y, rfl⟩ := hsurj y'
      rw [hord, hord] at hy'
      obtain ⟨r, ⟨hr, hrv⟩, hru⟩ := hR.2 y hy'
      refine ⟨u r, ⟨Finset.mem_image_of_mem u hr, ?_⟩, ?_⟩
      · rw [hcoe, hcoe, hcoe, ← map_sub i, hle]
        exact hrv
      · rintro r' ⟨hr', hr'v⟩
        obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 hr'
        rw [hcoe, hcoe, hcoe, ← map_sub i, hle] at hr'v
        rw [hru r0 ⟨hr0, hr'v⟩]
  · rw [hres, Finset.sum_image (fun x _ y _ h => huinj h)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hχ, hcoe, hψ]

end GlobalTheory.LocalFieldIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanAverages
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite.LiftOp
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_datVt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : GA D (Vc D i)) :
    levChi (Vc D i) (R.βV i) (R.datVt i t) κ = levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  have h := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.datVt i t).P (finE (Vc D i) κ)
  have h1 : Formalism.L2.DIV.ext1 (R.datVt i t).P.H (R.datVt i t).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ)) = 1 := by
    unfold Formalism.L2.DIV.ext1; split_ifs with hm
    · have : (⟨_, hm⟩ : (R.datVt i t).P.H) = 1 := Subtype.ext (Subgroup.mem_bot.1 hm)
      rw [this, map_one]
    · rfl
  unfold levChi
  rw [show R.datVt i t = withP (R.datVt i t) (R.datVt i t).P from rfl, h, h1, one_mul]
  rfl

theorem chF_mul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ₁ κ₂ : GA D (Vc D i)}
    (h₁ : finE (Vc D i) κ₁ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    (h₂ : finE (Vc D i) κ₂ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ₁ * κ₂) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ₁ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ₂ := by
  unfold levChi
  rw [map_mul, levFn_flag_mul h₁ h₂, Units.val_mul]

theorem parLev_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    finE (Vc D i) 1 ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
  rw [map_one]; exact Subgroup.one_mem _

theorem chF_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have h := chF_mul R i t (parLev_one R i t) (parLev_one R i t)
  rw [mul_one] at h
  have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) (1 : GA D (Vc D i))
  have : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem chF_inv (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (h : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ := by
  have hi : finE (Vc D i) κ⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [map_inv]; exact Subgroup.inv_mem _ h
  have e := chF_mul R i t h hi
  rw [mul_inv_cancel, chF_one] at e
  have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
  field_simp
  rw [mul_comm]; exact e.symm

theorem conj_mem_lev (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ j : GA D (Vc D i)} (hκG : κ ∈ GfC (Vc D i))
    (hκ : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    (hj : j ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) : κ * j * κ⁻¹ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
  refine ⟨(GfC (Vc D i)).mul_mem ((GfC (Vc D i)).mul_mem hκG hj.1) ((GfC (Vc D i)).inv_mem hκG), ?_⟩
  have hj2 : finE (Vc D i) j ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hj.2
  have hki : (finE (Vc D i) κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) :=
    Subgroup.inv_mem _ hκ
  show finE (Vc D i) (κ * j * κ⁻¹) ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)
  rw [map_mul, map_mul, map_inv]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hκ hj2.1) hki, ?_⟩
  have h1 : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) j) = 1 := Subgroup.mem_bot.1 hj2.2
  rw [Formalism.L2.DIV.rTup_mul (Subgroup.mul_mem _ hκ hj2.1) hki, Formalism.L2.DIV.rTup_mul hκ hj2.1, h1,
    Formalism.L2.DIV.rTup_inv hκ, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem typeVec_move (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hP : R.FullP) {κ : GA D (Vc D i)}
    (hκG : κ ∈ GfC (Vc D i))
    (hκ : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : TypeVec R i t φ) : TypeVec R i t (R.ωP i t (κ⁻¹, 1) φ) := by
  refine ⟨(hP i t).datum.om_pres _ φ hφ.1, fun j hj => ?_⟩
  have hc := conj_mem_lev R i t hκG hκ hj
  have e : ((j, 1) : GA D (Vc D i) × GA D (Wc D i)) * (κ⁻¹, 1) = (κ⁻¹, 1) * (κ * j * κ⁻¹, 1) := by
    simp only [Prod.mk_mul_mk, mul_one]; congr 1; group
  have hj2 : finE (Vc D i) j ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hj.2.1
  have hki : finE (Vc D i) κ⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [map_inv]; exact Subgroup.inv_mem _ hκ
  have hchi : levChi (Vc D i) (R.βV i) (R.datVt i t) (κ * j * κ⁻¹) = levChi (Vc D i) (R.βV i) (R.datVt i t) j := by
    rw [levChi_datVt, levChi_datVt, chF_mul R i t (by rw [map_mul]; exact Subgroup.mul_mem _ hκ hj2) hki,
      chF_mul R i t hκ hj2, chF_inv R i t hκ]
    have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
    field_simp
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hφ.2 _ hc, map_smul, hchi]

theorem levG_flag1 (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) = levG (Vc D i) (R.βV i) (R.datVt i t) := rfl

theorem pi_lift_indep (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hP : R.FullP) {g0 : Formalism.L2.DIV.G0 (R.datVt i t).Pg (R.datVt i t).r}
    {κ κ' : GA D (Vc D i)} (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (hκ' : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ')
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : TypeVec R i t φ) :
    (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ')⁻¹ • R.ωP i t (κ'⁻¹, 1) φ =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.ωP i t (κ⁻¹, 1) φ := by
  have hd : κ⁻¹ * κ' ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
    have h0 := lift_div_mem hκ hκ'
    rw [levG_flag1] at h0
    exact h0
  have hdi : (κ⁻¹ * κ')⁻¹ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := Subgroup.inv_mem _ hd
  have hm := typeVec_move R i t hP hκ.1 hκ.2.1 hφ
  have e : ((κ'⁻¹, 1) : GA D (Vc D i) × GA D (Wc D i)) = ((κ⁻¹ * κ')⁻¹, 1) * (κ⁻¹, 1) := by
    simp only [Prod.mk_mul_mk, mul_one]; congr 1; group
  have hdp : finE (Vc D i) (κ⁻¹ * κ') ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hd.2.1
  have hc : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ' =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ⁻¹ * κ') := by
    rw [← chF_mul R i t hκ.2.1 hdp, mul_inv_cancel_left]
  rw [e, map_mul, Module.End.mul_apply, hm.2 _ hdi, levChi_datVt, chF_inv R i t hdp, hc, smul_smul]
  congr 1
  have h1 := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
  have h2 := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) (κ⁻¹ * κ')
  field_simp

end GlobalTheory.DownLift.GenFinite.LiftOp

namespace GlobalTheory.DownLift.GenFinite
open LiftOp

theorem cleanSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ ∧ GlobalTheory.DownLift.GenFinite.Clean R i t φ} ∪ GlobalTheory.DownLift.GenFinite.AvgIm R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hf
  by_cases hex : ∃ κ : G → GA D (Vc D i), IsLifts R i t κ
  swap
  · exact Submodule.subset_span (Or.inl ⟨hf, fun PP a _ tr ε _ κ hκ => absurd ⟨κ, hκ⟩ hex⟩)
  obtain ⟨κ, hκ⟩ := hex
  let S : Submodule ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    { carrier := {φ | TypeVec R i t φ}
      add_mem' := fun {a b} ha hb => ⟨theta_add ha.1 hb.1, fun j hj => by rw [map_add (f := _), ha.2 j hj, hb.2 j hj, smul_add]⟩
      zero_mem' := ⟨by simpa using theta_smul (0 : ℂ) hf.1, fun j hj => by rw [map_zero, smul_zero]⟩
      smul_mem' := fun c a ha => ⟨theta_smul c ha.1, fun j hj => by
        rw [map_smul, ha.2 j hj, smul_comm]⟩ }
  have hSm : ∀ φ, φ ∈ S ↔ TypeVec R i t φ := fun _ => Iff.rfl
  let π : G → Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹ • R.ωP i t ((κ g)⁻¹, 1)
  have hπ : ∀ g φ, π g φ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹ • R.ωP i t ((κ g)⁻¹, 1) φ :=
    fun _ _ => rfl
  have hS : ∀ g, ∀ v ∈ S, π g v ∈ S := by
    intro g v hv
    rw [hπ]; exact S.smul_mem _ ((hSm _).2 (typeVec_move R i t hP (hκ g).1 (hκ g).2.1 ((hSm _).1 hv)))
  have hlift1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG 1) 1 :=
    ⟨Subgroup.one_mem _, parLev_one R i t, by rw [map_one, Formalism.L2.DIV.rTup_one, map_one]; rfl⟩
  have h1 : ∀ v ∈ S, π 1 v = v := by
    intro v hv
    rw [hπ, pi_lift_indep R i t hP hlift1 (hκ 1) ((hSm _).1 hv), chF_one, inv_one, one_smul, inv_one,
      ← Prod.one_eq_mk, map_one]
    rfl
  have hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v) := by
    intro g h v hv
    have hl : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG (g * h)) (κ g * κ h) := by
      refine ⟨(GfC (Vc D i)).mul_mem (hκ g).1 (hκ h).1, ?_, ?_⟩
      · rw [map_mul]; exact Subgroup.mul_mem _ (hκ g).2.1 (hκ h).2.1
      · rw [map_mul, Formalism.L2.DIV.rTup_mul (hκ g).2.1 (hκ h).2.1, (hκ g).2.2, (hκ h).2.2, map_mul]; rfl
    rw [hπ, pi_lift_indep R i t hP hl (hκ (g * h)) ((hSm _).1 hv), hπ, hπ, map_smul, smul_smul,
      ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, chF_mul R i t (hκ g).2.1 (hκ h).2.1, _root_.mul_inv_rev,
      _root_.mul_inv_rev]
  let C : Set (G → ℂ) := {c | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ),
    (ε = 1 ∨ ε = -1) ∧ c = mirC R i PP a tr ε}
  have hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C := by
    rintro c ⟨PP, a, ha, tr, ε, hε, rfl⟩ x
    obtain ⟨a', ha', he⟩ := _root_.GlobalTheory.DownLift.GenFinite.mirC_conj D G Pl0 T A Ks R i PP a ha tr ε x
    exact ⟨PP, a', ha', tr, ε, hε, funext he⟩
  have havg : ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ) (κ' : G → GA D (Vc D i)), IsLifts R i t κ' →
      ∀ w ∈ S, avgW R i t PP a tr ε κ' w = ∑ g, mirC R i PP a tr ε g • π g w := by
    intro PP a tr ε κ' hκ' w hw
    unfold avgW
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hπ, ← pi_lift_indep R i t hP (hκ g) (hκ' g) ((hSm _).1 hw), smul_smul]
  have key := GlobalTheory.T.mem_span_annihilated_union_class_averages S π hS h1 hmul C hC f hf
  refine Submodule.span_mono ?_ key
  rintro w (⟨hwS, hw⟩ | ⟨c, ⟨PP, a, ha, tr, ε, hε, rfl⟩, w', hw'S, rfl⟩)
  · exact Or.inl ⟨hwS, fun PP a ha tr ε hε κ' hκ' => by
      rw [havg PP a tr ε κ' hκ' w hwS]; exact hw _ ⟨PP, a, ha, tr, ε, hε, rfl⟩⟩
  · exact Or.inr ⟨PP, a, ha, tr, ε, hε, κ, hκ, w', hw'S.1, (havg PP a tr ε κ hκ w' hw'S).symm⟩

end GlobalTheory.DownLift.GenFinite
end
end

