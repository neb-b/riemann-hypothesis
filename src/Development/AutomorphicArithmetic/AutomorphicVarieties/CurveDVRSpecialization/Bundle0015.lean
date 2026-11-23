module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionLevelKernel
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (M : ℕ)
    (hM : ∀ v : W.Plc (W.Lp L), ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → v ∈ V.S') (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg' : toGS Ω V.S' (W.resP L Ω g) = 1 := congrArg Subtype.val hg
  have hNS : W.resP L Ω g ∈ NS Ω V.S' := by
    unfold toGS at hg'
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg'
  let Kp : Subgroup (G (W.Lp L) Ω) := K.map (W.resP L Ω)
  have hKp : IsClosed (Kp : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hK.isCompact).image W.continuous_resP).isClosed
  have hX : ∀ v : W.Plc (W.Lp L), v ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∀ τ ∈ Ine (F := W.Lp L) A, τ ∈ Kp := by
    intro v hv A hA τ hτ
    obtain ⟨t, ht⟩ := s.unr A v hA hτ
    have hM' : ¬ A.valuation (M : Ω) < 1 := by
      rw [natCast_place hA]
      exact fun h => hv (hM v h)
    have htI : t ∈ Ine (F := L) A := by
      have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) A := by
        rw [ht]
        exact hτ
      exact h1
    exact ⟨t, hI A hM' htI, ht⟩
  have hNSle : NS Ω V.S' ≤ Kp := by
    letI : MulAction (G (W.Lp L) Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
    unfold NS
    apply Subgroup.topologicalClosure_minimal _ _ hKp
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, hx, hconj⟩ := hy
    simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hv, A, hA, hxA⟩ := hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    subst hc
    have hlift : IsLift (RingEquiv.refl (W.Lp L)) (c⁻¹).toRingEquiv := fun z => (c⁻¹).commutes z
    have hmem : ∀ z : Ω, (c⁻¹).toRingEquiv z ∈ A ↔ z ∈ c • A := by
      intro z
      exact (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := c) (S := A) (x := z)).symm
    have h1 := conjGal_mem_Ine hlift hmem hxA
    have heq : conjGal hlift x = c * x * c⁻¹ := AlgEquiv.ext fun z => rfl
    have hcA : ∀ z : Ω, c.toRingEquiv z ∈ c • A ↔ z ∈ A := by
      intro z
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := c) (S := A) (x := z)
    have hplace : IsPlaceOver (c • A) v := by
      intro z
      have hz : c.toRingEquiv ((algebraMap (W.Lp L) Ω) (z : W.Lp L)) = (algebraMap (W.Lp L) Ω) (z : W.Lp L) :=
        c.commutes _
      rw [← hz, val_lt_one hcA]
      exact hA z
    rw [← heq]
    exact hX v hv (c • A) hplace _ h1
  obtain ⟨g', hg'K, hg'eq⟩ := hNSle hNS
  have hgg : g' = g := by
    ext z
    exact DFunLike.congr_fun hg'eq z
  rw [← hgg]
  exact hg'K

private theorem coef_algebraMap_padicInt_eq (l : ℕ) [Fact l.Prime] (c₁ : Coef l) (z : ℤ_[l]) :
    ((algebraMap c₁.O c₁.O (algebraMap ℤ_[l] c₁.O z) : c₁.O) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := by
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  change algebraMap ℤ_[l] (PadicAlgCl l) z = _
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rfl

theorem UpperTheory.frame_criterion_level_kernel :
    UpperTheory.V.Pr.CrKap := by
  unfold UpperTheory.V.Pr.CrKap
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS c₁ ι n ka hka hO
  have hcont : Continuous ka := hka.alg.1
  let f : G L Ω →* c₁.O :=
    { toFun := fun g => ⟨(ka g : Qbar l), hO g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  let ka0 : G L Ω →* (c₁.O)ˣ := f.toHomUnits
  have hMS : ∀ v : W.Plc (W.Lp L), ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → v ∈ V.S' := by
    intro v hv
    rw [hS]
    by_cases hl : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact Or.inl hl
    · exact Or.inr (Or.inl ((x.St v).2 ⟨hv, hl⟩))
  have hKc : IsClosed (ka.ker : Set (G L Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hcont
  have hker : V.pr.ker ≤ ka.ker :=
    ker_pr_le V M hMS ka.ker hKc (fun A hA t ht => (MonoidHom.mem_ker).2 (hka.unr A hA t ht))
  have hker0 : V.pr.ker ≤ ka0.ker := by
    intro g hg
    have h1 : ka g = 1 := hker hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply Subtype.ext
    change (ka g : Qbar l) = ((1 : (Qbar l)ˣ) : Qbar l)
    rw [h1]
  have hsurj := pr_surj V
  let κ : V.frame.G₀ →* (c₁.O)ˣ :=
    V.pr.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨ka0, hker0⟩
  have hκ : ∀ g, κ (V.pr g) = ka0 g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  let φ : (c₁.O)ˣ →* (Qbar l)ˣ := Units.map (c₁.O.val : c₁.O →* Qbar l)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hab
  have hφka : ∀ g, φ (ka0 g) = ka g := fun g => Units.ext rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro g
    rw [hκ g]
    rfl
  · rw [(X.So.adicCont l c₁).2]
    haveI : IsClosed (NS Ω V.S' : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
    have hprc : Continuous V.pr := V.pr_cont W.continuous_resP
    have hq : Topology.IsQuotientMap V.pr := IsClosedMap.isQuotientMap hprc.isClosedMap hprc hsurj
    have hfun : (fun g : ↥V.η.ker => ((κ g : (c₁.O)ˣ) : c₁.O)) ∘ V.pr =
        fun g => (⟨(ka g : Qbar l), hO g⟩ : c₁.O) := by
      funext g
      simp only [Function.comp_apply, hκ]
      rfl
    have hc2 : Continuous ((fun g : ↥V.η.ker => ((κ g : (c₁.O)ˣ) : c₁.O)) ∘ V.pr) := by
      rw [hfun]
      exact (Units.continuous_val.comp hcont).subtype_mk hO
    exact hq.continuous_iff.2 hc2
  · intro g0
    obtain ⟨g, rfl⟩ := hsurj g0
    have hr : V.η (toGS Ω V.S' (W.resP L Ω g)) = 1 := (V.hη _).2 ⟨g, rfl⟩
    have hτr : s.c * W.resP L Ω g * s.c⁻¹ ∈ (W.resP L Ω).range := by
      apply (V.hη _).1
      simp only [map_mul, map_inv, hr, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hτr
    have hconjpr : V.frame.conj (V.pr g) = V.pr g' := by
      apply Subtype.ext
      change toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω g) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω g')
      rw [hg', map_mul, map_mul, map_inv]
    have hσ : galEmb ℚ L Ω g' = σ * galEmb ℚ L Ω g * σ⁻¹ := by
      rw [← galEmb_resP g', ← galEmb_resP g, hg', map_mul, map_mul, map_inv, x.c]
    have hk := hka.conj g g' hσ
    have he : φ (V.frame.eps c₁.O c₁.O (V.pr g)) = cycBar L Ω l g := by
      apply Units.ext
      have hε : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
      change ((algebraMap c₁.O c₁.O (algebraMap ℤ_[l] c₁.O ((V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]))) : c₁.O) : Qbar l) =
        algebraMap ℚ_[l] (Qbar l) (((cycZ L Ω l g : ℤ_[l])) : ℚ_[l])
      rw [hε, coef_algebraMap_padicInt_eq]
    rw [hconjpr, hκ, hκ]
    apply hφ
    rw [map_mul, map_zpow, hφka, hφka, he]
    exact hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionResidual
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr

end UpperTheory.V.Pr

theorem UpperTheory.frame_criterion_residual :
    UpperTheory.V.Pr.CrResid := by
  intro l _ O _ _ _ F G n hn hk hg π hπ hs hc κ hκ hκe
  let χ : Fin n → G.G₀ →* (ResidueField O)ˣ := fun i =>
    { toFun := fun g => F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul, Subgroup.coe_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }
  have hψ : IsOpen ((F.Ψ.comp (F.del.ker.subtype.comp π)).ker : Set G.G₀) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact hk.preimage (continuous_subtype_val.comp hπ)
  have hκo : IsOpen ((W.pushCh (residue O) κ).ker : Set G.G₀) := by
    have h1 := (hκ 1).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal O ^ 1) 1)
    convert h1 using 1
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Ideal.Quotient.eq, pow_one, Units.ext_iff]
    show residue O (κ g : O) = 1 ↔ _
    rw [← map_one (residue O)]
    exact Ideal.Quotient.eq
  have hopen : ∀ i, IsOpen ((χ i).ker : Set G.G₀) := by
    intro i
    refine Subgroup.isOpen_mono (H₁ := (F.Ψ.comp (F.del.ker.subtype.comp π)).ker ⊓ (W.pushCh (residue O) κ).ker) ?_ (by rw [Subgroup.coe_inf]; exact hψ.inter hκo)
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    show F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g = 1
    rw [hg.2, mul_one]
    have : F.Ψ (π g : F.Γ) = 1 := hg.1
    rw [this, one_zpow]
  have hinj : Function.Injective χ := by
    intro i j hij
    obtain ⟨g, hg0⟩ := hs F.g0
    have h := DFunLike.congr_fun hij g
    change F.Ψ (π g : F.Γ) ^ Fr.w n i * _ = F.Ψ (π g : F.Γ) ^ Fr.w n j * _ at h
    rw [mul_right_cancel_iff, hg0] at h
    have key : F.Ψ (F.g0 : F.Γ) ^ (Fr.w n i - Fr.w n j) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have hu2 : F.Ψ (F.g0 : F.Γ) ^ (2:ℤ) ≠ 1 := by exact_mod_cast hg
    have hu1 : F.Ψ (F.g0 : F.Γ) ≠ 1 := by
      intro h1
      apply hu2
      rw [h1, one_zpow]
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [Fr.w] at key ⊢
    all_goals first
      | exact hg key
      | exact hu1 key
      | exact hu2 key
      | exact hu1 (inv_eq_one.mp key)
      | exact hg (inv_eq_one.mp (by simpa [zpow_neg] using key))
  have hw : ∀ i : Fin n, Fr.w n (Fin.rev i) = - Fr.w n i := by
    intro i
    rcases hn with rfl | rfl <;> fin_cases i <;> simp [Fr.w] <;> decide
  have hΨc : ∀ g, F.Ψ (π (G.conj g) : F.Γ) = F.Ψ (π g : F.Γ) := by
    intro g
    rw [hc]
    simp [Fr.Frame.conj, MulAut.conjNormal_apply]
  have heps : ∀ g, Units.map (residue O : O →* ResidueField O) (G.eps O O g) = G.eps O (ResidueField O) g := by
    intro g
    ext
    simp [W.GFrame.eps, W.pushCh]
  have hκc : ∀ g, W.pushCh (residue O) κ (G.conj g) = (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (W.pushCh (residue O) κ g)⁻¹ := by
    intro g
    have h1 : κ (G.conj g) = (G.eps O O g) ^ (1 - (n:ℤ)) * (κ g)⁻¹ := by
      rw [← hκe g, mul_comm (κ g) (κ (G.conj g)), mul_inv_cancel_right]
    show Units.map (residue O : O →* ResidueField O) (κ (G.conj g)) = _
    rw [h1, map_mul, map_inv, map_zpow, heps]
    rfl
  have hstar : ∀ i g, (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (χ i (G.conj g))⁻¹ = χ (Fin.rev i) g := by
    intro i g
    show _ * (F.Ψ (π (G.conj g) : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ (G.conj g))⁻¹ = F.Ψ (π g : F.Γ) ^ Fr.w n (Fin.rev i) * W.pushCh (residue O) κ g
    rw [hΨc, hκc, hw, zpow_neg, mul_inv, mul_inv, inv_inv, mul_left_comm, mul_inv_cancel_left]
  have hpolar : G.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
    intro B _ _ _ _ y
    let f : Fin n → G.G₀ →* B := fun i => (algebraMap (ResidueField O) B : ResidueField O →* B).comp ((Units.coeHom (ResidueField O)).comp (χ i))
    have hdiag : ∀ z : MonoidAlgebra B G.G₀, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => MonoidAlgebra.lift B B G.G₀ (f i) z) := by
      intro z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
        rw [map_add (f := _), hx, hy, Matrix.diagonal_add]
        congr 1
        ext i
        simp [map_add (f := _)]
      | single g b =>
        ext i j
        simp [f, W.GDet.repAlg, W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]
    have hepsB : ∀ g, Units.map (algebraMap (ResidueField O) B : ResidueField O →* B) (G.eps O (ResidueField O) g) = G.eps O B g := by
      intro g
      ext
      simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O (ResidueField O) B]
    have hs1 : ∀ (g : G.G₀) (b : B), G.star O B n (MonoidAlgebra.single g b) = MonoidAlgebra.single (G.conj g)⁻¹ (b * ((G.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
      intro g b
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
    have hrev : ∀ i z, MonoidAlgebra.lift B B G.G₀ (f i) (G.star O B n z) = MonoidAlgebra.lift B B G.G₀ (f (Fin.rev i)) z := by
      intro i z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp [W.GFrame.star]
      | add x y hx hy =>
        have hadd : G.star O B n (x + y) = G.star O B n x + G.star O B n y := by simp [W.GFrame.star]
        rw [hadd, map_add (f := _), map_add (f := _), hx, hy]
      | single g b =>
        rw [hs1 g b, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, smul_eq_mul, smul_eq_mul, mul_assoc]
        congr 1
        rw [← hepsB g, ← map_zpow, Units.coe_map]
        show _ = algebraMap (ResidueField O) B ((χ (Fin.rev i) g : (ResidueField O)ˣ) : ResidueField O)
        rw [← hstar i g, Units.val_mul, map_mul]
        simp [f]
    show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (G.star O B n y)) = Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
    rw [hdiag, hdiag, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [hrev]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  refine ⟨⟨χ, hopen, hinj, hpolar, fun v i => (χ i).comp (G.φ v), ?_, fun _ _ => 1, ?_⟩, ?_, ?_⟩
  · intro v i
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (hopen i).preimage (G.φ_cont v)
  · intro v i g _
    rfl
  · intro i g
    rfl
  · intro v i g
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ResidualOkOfLocalCharsRestrict
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

section
open Polynomial UpperTheory.V.W

private theorem chi_ofRep' {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  show Matrix.det (GDet.repAlg ρ A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)) = _
  rw [map_sub]
  congr 2
  simp [GDet.repAlg, MonoidAlgebra.lift_single, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

private theorem prod_diagonal {n : ℕ} {A : Type} [CommRing A] (L : List (Fin n → A)) :
    (L.map Matrix.diagonal).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons, Matrix.diagonal_mul_diagonal]
    rfl

private theorem rep_oEl {l : ℕ} [Fact l.Prime] {G : GFrame l} {k : Type} [CommRing k] {n : ℕ}
    (χ : Fin n → G.G₀ →* kˣ) (v : G.Vl) (ψ : Fin n → G.Gv v →* kˣ) (h : ∀ i g, ψ i g = χ i (G.φ v g))
    (g : Fin n → G.Gv v) :
    GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C (G.oEl v ψ g)) = 0 := by
  have hf : ∀ i, GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C
      (MonoidAlgebra.single (G.φ v (g i)) 1 - MonoidAlgebra.single 1 ((ψ i (g i) : kˣ) : k))) =
      Matrix.diagonal (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)) := by
    intro i
    simp [GDet.repAlg, MonoidAlgebra.lift_single, diagRep, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_sub]
  unfold GFrame.oEl
  rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  simp only [Function.comp_def, hf]
  have key : (List.ofFn fun i => Matrix.diagonal
      (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k))) =
      (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).map
        Matrix.diagonal := by
    rw [List.map_ofFn]
    rfl
  rw [key, prod_diagonal]
  have hz : (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).prod
      = 0 := by
    funext j
    rw [List.prod_ofFn, Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [h]
  rw [hz]
  exact Matrix.diagonal_zero

end

theorem UpperTheory.residual_ok_of_local_chars_restrict :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l]
      {G : W.GFrame l} {n : ℕ} (r : W.Resid G O n), 1 ≤ n →
      (∀ v i g, r.psib v i g = r.chib i (G.φ v g)) → r.Ok := by
  intro l _ O _ _ _ _ G n r hn hps
  refine ⟨fun v g h => ?_, fun v i g => ?_⟩
  · simp only [W.Resid.Dbar, W.GDet.tr, W.GDet.lam]
    rw [chi_ofRep', map_mul, map_mul, rep_oEl r.chib v (r.psib v) (hps v) g, mul_zero, sub_zero,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · rw [(W.residualDatum_inertia_characters_trivial l G O n r v i g).1, (W.residualDatum_inertia_characters_trivial l G O n r v i g).2]
end

