module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlaces
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := _root_.GlobalTheory.Nef.existsUnique_centre k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainConjugateUnitaryAdeli
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarConj

variable {D : D7}

theorem isFundamentalDomain_image {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) (h : IsFundamentalDomain Γ 𝓕 μ) :
    IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
  rw [e]
  exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
    (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
    ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
      fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
    fun γ y => by
      show φ.symm (φ γ * y) = γ * φ.symm y
      rw [map_mul, φ.symm_apply_apply]

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp [cA, sigR, incA, inclR, Algebra.TensorProduct.map_tmul]

theorem incA_inj : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 D.host.F) (K := D.host.F))

def conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D V :=
  ⟨GeneralLinearGroup.map (cA D) u.1, by
    have hu : u.1.1ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * u.1.1.map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
    have e : (u.1.1.map (cA D)).map (cA D) = u.1.1 := Matrix.ext fun _ _ => cA_cA _
    show Formalism.UG.cT (cA D) (u.1.1.map (cA D)) * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * u.1.1.map (cA D)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram
    rw [Formalism.UG.cT, e]
    generalize u.1.1 = M at hu ⊢
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hu
    have k : incA D c⁻¹ * incA D c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have := congrArg (incA D c⁻¹ • ·) hu
    simpa only [smul_smul, k, one_smul] using this⟩

def conjE (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := conjU V c h
  invFun := conjInv V c hc h
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  right_inv u := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  map_mul' a b := Subtype.ext (by
    show GeneralLinearGroup.map (cA D) (matHom V (a * b)) = GeneralLinearGroup.map (cA D) (matHom V a) *
      GeneralLinearGroup.map (cA D) (matHom V b)
    rw [map_mul, map_mul])

theorem continuous_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjInv V c hc h) := by
  have h1 : Continuous (fun u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J => u.1) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  · exact (Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)

theorem mem_ratU_iff (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (g : GA D V) :
    g ∈ GQ V ↔ conjE V c hc h g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  have hg : Formalism.UG.cT (cA D) g.1.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * g.1.1 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram := g.2
  constructor
  · intro hq
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hq)
    refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) x, ?_⟩
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hx
    show incA D (D.sp.cm.sig (x.1 i j)) = cA D (g.1.1 i j)
    rw [← this, ← cA_incA]
    rfl
  · intro hq
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 hq
    have hw' : ∀ i j, incA D (w.1 i j) = cA D (g.1.1 i j) := fun i j =>
      congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hw
    have hx : ∀ i j, incA D (D.sp.cm.sig (w.1 i j)) = g.1.1 i j := fun i j => by
      rw [← cA_incA, hw', cA_cA]
    let x := GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) w
    have hxm : x.1.map (incA D) = g.1.1 := Matrix.ext fun i j => hx i j
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, Units.ext (Matrix.ext fun i j => hx i j)⟩)
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1).map (incA D) =
        V.gram.map (incA D) := by
      rw [Matrix.map_mul, Matrix.map_mul, hxm]
      have e1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1).map (incA D) = Formalism.UG.cT (cA D) g.1.1 := by
        rw [← hxm]
        ext i j
        simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
        exact (cA_incA _).symm
      rw [e1]
      exact hg
    exact Matrix.ext fun i j => incA_inj (congrFun (congrFun key i) j)

theorem haarConj : ∀ {D : D7} (V : HSp D) (c : D.host.E), c ≠ 0 → ∀ {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hJ : J = c • V.gram)
    (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∃ dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J), (ν.map (conjU V c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) dom (ν.map (conjU V c hJ)) := by
  intro D V c hc J hJ ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (conjE V c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c hJ
  have c2 : Continuous (conjE V c hc hJ).symm := continuous_conjInv V c hc hJ
  exact ⟨conjE V c hc hJ '' fd, MulEquiv.isHaarMeasure_map ν (conjE V c hc hJ) c1 c2,
    isFundamentalDomain_image (conjE V c hc hJ) c1.measurable c2.measurable (GQ V) _ (mem_ratU_iff V c hc hJ) ν fd hfd⟩

end GlobalTheory.HaarConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLattice
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LattIota

variable {A O M : Type} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M] {ι : Type}
  (θ : A →+* O) (hs : Function.Surjective θ) (R : (ι → A) →ₛₗ[θ] M)
  (hR : ∀ s : ι → A, (∀ i, θ (s i) = 0) → R s = 0)

include hR in
theorem eq_of_theta_eq {s s' : ι → A} (h : ∀ i, θ (s i) = θ (s' i)) : R s = R s' := by
  rw [← sub_eq_zero, ← map_sub]
  exact hR _ fun i => by rw [Pi.sub_apply, map_sub, h, sub_self]

def descend : (ι → O) →ₗ[O] M where
  toFun ρ := R (fun i => Function.surjInv hs (ρ i))
  map_add' ρ ρ' := by
    rw [← map_add (f := _)]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]
  map_smul' c ρ := by
    have h1 : (c • R (fun i => Function.surjInv hs (ρ i)) : M) =
        θ (Function.surjInv hs c) • R (fun i => Function.surjInv hs (ρ i)) := by
      rw [Function.surjInv_eq hs]
    rw [RingHom.id_apply, h1, ← LinearMap.map_smulₛₗ]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]

theorem descend_comp (s : ι → A) : descend θ hs R hR (fun i => θ (s i)) = R s :=
  eq_of_theta_eq θ R hR fun i => Function.surjInv_eq hs _

variable [Fintype ι]

def dotL (ρ : ι → O) : (ι → O) →ₗ[O] O where
  toFun w := ρ ⬝ᵥ w
  map_add' := dotProduct_add ρ
  map_smul' c w := by rw [dotProduct_smul, RingHom.id_apply]

end GlobalTheory.LattIota

namespace GlobalTheory.LattIota

theorem iota_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG M _ _ r π hrs hker hπ
  obtain ⟨D, e, fil, lie, hal, hb⟩ := hG
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace p C v O hv ε hε G G.height D e fil hal
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by
    simpa [zeta] using hε 1
  obtain ⟨hdom, -, hkerθ, hsθ, hν, hξ, -⟩ := _root_.GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  obtain ⟨hFG, hrangeFil, -, hνFil, -, -⟩ :=
    GlobalTheory.Sandwich.HodgeTateBound.bound p C v O hv ε hε1 ℤ_[p] G.height D
  obtain ⟨hFin, hProj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hkerθ]; exact Ideal.mem_span_singleton_self _
  let R : (Fin G.height → Ainf p O) →ₛₗ[WittVector.fontaineTheta O p] M :=
    r.comp (L : (Fin G.height → Ainf p O) →ₗ[Ainf p O] latt G)
  have hR : ∀ s : Fin G.height → Ainf p O, (∀ i, WittVector.fontaineTheta O p (s i) = 0) →
      R s = 0 := by
    intro s hs0
    have hu : ∀ i, ∃ u, u * xi ε = s i := fun i => by
      rw [← Ideal.mem_span_singleton', ← hkerθ]; exact hs0 i
    choose u hu using hu
    have hsu : s = xi ε • u := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hu]
    change r (L s) = 0
    rw [hker, hsu, map_smul]
    exact ⟨_, rfl⟩
  let Φ := descend _ hsθ R hR
  have hΦ : ∀ s, Φ (fun i => WittVector.fontaineTheta O p (s i)) = r (L s) := fun s =>
    descend_comp _ hsθ R hR s
  have hlift : ∀ ρ : Fin G.height → O, ∃ s : Fin G.height → Ainf p O,
      (fun i => WittVector.fontaineTheta O p (s i)) = ρ := fun ρ =>
    ⟨fun i => Function.surjInv hsθ (ρ i), funext fun i => Function.surjInv_eq hsθ _⟩
  have hΦs : Function.Surjective Φ := by
    intro m
    obtain ⟨y, rfl⟩ := hrs m
    obtain ⟨s, rfl⟩ := L.surjective y
    exact ⟨_, hΦ s⟩
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ρ hρ
    obtain ⟨s, rfl⟩ := hlift ρ
    rw [hΦ, hker] at hρ
    obtain ⟨n, hn⟩ := hρ
    have hs : s = xi ε • L.symm n := by
      apply L.injective; rw [map_smul, L.apply_symm_apply, hn]
    funext i
    rw [hs, Pi.smul_apply, smul_eq_mul, map_mul, hθξ, zero_mul, Pi.zero_apply]
  have hπHT : ∀ s t, π (r (L s)) (hodgeTate G t) =
      (fun i => WittVector.fontaineTheta O p (s i)) ⬝ᵥ (fil (hodgeTate G t) : Fin G.height → O) := by
    intro s t
    rw [hπ, hL, ← hal, RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    rfl
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i; funext j
    by_cases hij : j = i
    · subst hij; simp [toO]
    · simp [toO, Pi.single_apply, hij]
  have hext : ∀ f₁ f₂ : G.dual.omega →ₗ[O] O,
      (∀ t, f₁ (hodgeTate G t) = f₂ (hodgeTate G t)) → f₁ = f₂ := by
    intro f₁ f₂ hf
    let g : (G.dual.omega →ₗ[O] O) → (Fin G.height → O) →ₗ[O] O := fun f =>
      f ∘ₗ fil.symm.toLinearMap ∘ₗ (D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩))
    have key : ∀ f t, g f (toO e t) = f (hodgeTate G t) := by
      intro f t
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) (toO e t) =
          fil (hodgeTate G t) := Subtype.ext (hal t)
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearEquiv.symm_apply_apply]
    have hg : g f₁ = g f₂ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      change g f₁ (Pi.single i 1) = g f₂ (Pi.single i 1)
      rw [← hsingle, key, key, hf]
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, hw⟩ := hνFil _ (fil x).2
    have hgx : ∀ f, g f w = WittVector.fontaineTheta O p (nu ε) * f x := by
      intro f
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) w =
          WittVector.fontaineTheta O p (nu ε) • fil x := Subtype.ext hw
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearEquiv.symm_apply_apply, smul_eq_mul]
    exact mul_left_cancel₀ hν (by rw [← hgx, ← hgx, hg])
  have hπΦ : ∀ ρ x, π (Φ ρ) x = ρ ⬝ᵥ (fil x : Fin G.height → O) := by
    intro ρ
    obtain ⟨s, rfl⟩ := hlift ρ
    have := hext (π (Φ (fun i => WittVector.fontaineTheta O p (s i))))
      (dotL (fun i => WittVector.fontaineTheta O p (s i)) ∘ₗ D.Fil.subtype ∘ₗ fil.toLinearMap)
      (fun t => by rw [hΦ, hπHT]; rfl)
    intro x
    exact LinearMap.congr_fun this x
  let κ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  have hκ : ∀ w i, κ w i = lie (D.Fil.mkQ (Pi.single i 1)) w := fun w i => rfl
  have hk : ∀ w m, κ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := by
    intro w
    have : dotL (κ w) = (LinearMap.applyₗ w : Module.Dual O G.omega →ₗ[O] O) ∘ₗ
        lie.toLinearMap ∘ₗ D.Fil.mkQ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      simp [dotL, hκ]
    intro m
    exact LinearMap.congr_fun this m
  have hκi : Function.Injective κ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine (Module.forall_dual_apply_eq_zero_iff O w).1 fun φ => ?_
    obtain ⟨q, rfl⟩ := lie.surjective φ
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [← hk, hw, zero_dotProduct]
  refine ⟨Φ ∘ₗ κ, hΦi.comp hκi, fun m => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨ρ, rfl⟩ := hΦs m
    have hρ : D.Fil ≤ LinearMap.ker (dotL ρ) := fun f hf => by
      obtain ⟨x, hx⟩ := fil.surjective ⟨f, hf⟩
      have := LinearMap.congr_fun h0 x
      rw [hπΦ, hx] at this
      exact this
    let ψ : ((Fin G.height → O) ⧸ D.Fil) →ₗ[O] O := D.Fil.liftQ (dotL ρ) hρ
    let w := (Module.evalEquiv O G.omega).symm (ψ ∘ₗ lie.symm.toLinearMap)
    have hw : ∀ φ : G.Lie, φ w = ψ (lie.symm φ) := fun φ => by
      change (Module.evalEquiv O G.omega w) φ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    refine ⟨w, ?_⟩
    change Φ (κ w) = Φ ρ
    congr 1
    funext i
    rw [hκ, hw, LinearEquiv.symm_apply_apply]
    simp [ψ, dotL]
  · rintro ⟨w, rfl⟩
    refine LinearMap.ext fun x => ?_
    change π (Φ (κ w)) x = 0
    rw [hπΦ, hk, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (fil x).2, map_zero]
    rfl
  · intro χ y hy
    let sχ : Fin G.height → Ainf p O := fun i =>
      ofPadic p O (epsPairing hε G (e.symm (Pi.single i 1)) χ)
    have hpair : ∀ t, sχ ⬝ᵥ (fun i => ofPadic p O (e t i)) = ofPadic p O (epsPairing hε G t χ) := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hlin : epsPairing hε G t χ =
          ∑ i, e t i * epsPairing hε G (e.symm (Pi.single i 1)) χ := by
        conv_lhs => rw [ht]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [epsPairing, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hlin, map_sum]
      simp only [dotProduct, sχ, map_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hyL : y = L (sχ ᵥ* D.G) := by
      apply Subtype.ext
      refine LinearMap.ext fun t => ?_
      rw [hL, hy, ← dotProduct_mulVec, mulVec_mulVec, D.G_mul_F, smul_mulVec, one_mulVec,
        dotProduct_smul, hpair, smul_eq_mul]
    rw [hyL, ← hΦ]
    change Φ (κ (dlog G χ)) = _
    congr 1
    funext i
    rw [hκ, ← hb, LinearEquiv.symm_apply_apply, RingHom.map_vecMul]
    simp [bQuot, pairingO, Datum.bb, Matrix.toLin'_apply, vecMul, dotProduct, padicToO, sχ,
      mul_comm]

end GlobalTheory.LattIota
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory

theorem exists_int_add_conj_eq_one_of_base_good : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactLevelContinuousStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_compact_level_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  first | exact @GlobalTheory.ResLine.HtCont.isCompact_and_continuous | exact GlobalTheory.ResLine.HtCont.isCompact_and_continuous | (intros; apply GlobalTheory.ResLine.HtCont.isCompact_and_continuous <;> assumption)
end

