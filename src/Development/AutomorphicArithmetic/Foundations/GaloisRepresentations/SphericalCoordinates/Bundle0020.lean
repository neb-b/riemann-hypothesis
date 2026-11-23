module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem lin_eq_of_exp {g : ℕ} {Q : Type*} [Group Q] (e : (Fin g → ℂ) → Q) (A : AddSubgroup (Fin g → ℂ))
    (hA : DiscreteTopology A) (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ A)
    (M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, e (M z) = e (M' z)) : M = M' := by
  have hd : ∀ z, M z - M' z ∈ A := by
    intro z
    rw [← hker]
    have := hadd (M z - M' z) (M' z)
    rw [sub_add_cancel, h] at this
    exact mul_eq_right.mp this.symm
  refine LinearMap.ext fun z => ?_
  have key : ∀ r : ℝ, (r : ℂ) • (M z - M' z) ∈ A := fun r => by
    have := hd ((r : ℂ) • z)
    rwa [map_smul, map_smul, ← smul_sub] at this
  exact sub_eq_zero.mp (GlobalTheory.HeckeUnif.eq_zero_of_real_smul_mem A hA _ key)

private theorem exists_linearEquiv_of_isog {X : Scheme.{0}} {A B : Over X} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (g : ℕ) (hA : IsAbelianScheme A) (hAs : SmoothOfRelativeDimension g A.hom)
    (hB : IsAbelianScheme B) (hBs : SmoothOfRelativeDimension g B.hom) (y : Sp ℂ ⟶ X)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ A)) (E : (Fin g → ℂ) → (Over.mk y ⟶ B)) (he : IsExp y e) (hE : IsExp y E)
    (Ae Be : AddSubgroup (Fin g → ℂ)) (hAe : DiscreteTopology Ae) (hBe : DiscreteTopology Be)
    (hke : ∀ z, e z = 1 ↔ z ∈ Ae) (hkE : ∀ z, E z = 1 ↔ z ∈ Be)
    (ψ : A ⟶ B) (ψ' : B ⟶ A) [IsMonHom ψ] [IsMonHom ψ'] (d : ℕ) (hd : d ≠ 0)
    (h1 : ψ ≫ ψ' = (𝟙 A) ^ d) (h2 : ψ' ≫ ψ = (𝟙 B) ^ d) :
    ∃ H : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, E (H z) = e z ≫ ψ) ∧ (∀ z ∈ Ae, H z ∈ Be) ∧
      ∀ z ∈ Be, (d : ℂ) • H.symm z ∈ Ae := by
  have hol : ∀ {C C' : Over X} (u : (Fin g → ℂ) → (Over.mk y ⟶ C)) (f : C ⟶ C'), IsHolTo Set.univ (fun z => (u z).left) →
      IsHolTo Set.univ (fun z => (u z ≫ f).left) := by
    intro C C' u f hu
    have : (fun z => (u z ≫ f).left) = fun z => (u z).left ≫ f.left := funext fun z => by simp only [Over.comp_left]
    rw [this]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hu _
  obtain ⟨M₀, hM₀, -⟩ := GlobalTheory.HeckeUnif.existsUnique_linear_lift_of_hom X B g hB hBs y E (fun z => e z ≫ ψ) hE
    (fun z w => by rw [he.1, MonObj.mul_comp]) (hol e ψ he.2.2.1)
  obtain ⟨M₁, hM₁, -⟩ := GlobalTheory.HeckeUnif.existsUnique_linear_lift_of_hom X A g hA hAs y e (fun z => E z ≫ ψ') he
    (fun z w => by rw [hE.1, MonObj.mul_comp]) (hol E ψ' hE.2.2.1)
  have hpe : ∀ z, e ((d : ℂ) • z) = e z ^ d := fun z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact GlobalTheory.UPel.HT.unifCls_exp_nsmul e he.1 d z
  have hpE : ∀ z, E ((d : ℂ) • z) = E z ^ d := fun z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact GlobalTheory.UPel.HT.unifCls_exp_nsmul E hE.1 d z
  have h10 : M₁ ∘ₗ M₀ = (d : ℂ) • LinearMap.id := lin_eq_of_exp e Ae hAe he.1 hke _ _ fun z => by
    show e (M₁ (M₀ z)) = e ((d : ℂ) • z)
    rw [hM₁, hM₀, hpe, Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
  have h01 : M₀ ∘ₗ M₁ = (d : ℂ) • LinearMap.id := lin_eq_of_exp E Be hBe hE.1 hkE _ _ fun z => by
    show E (M₀ (M₁ z)) = E ((d : ℂ) • z)
    rw [hM₀, hM₁, hpE, Category.assoc, h2, MonObj.comp_pow, Category.comp_id]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  let H : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear M₀ ((d : ℂ)⁻¹ • M₁)
    (by
      rw [LinearMap.comp_smul, h01, smul_smul, inv_mul_cancel₀ hd', one_smul])
    (by
      rw [LinearMap.smul_comp, h10, smul_smul, inv_mul_cancel₀ hd', one_smul])
  refine ⟨H, fun z => hM₀ z, fun z hz => ?_, fun z hz => ?_⟩
  · rw [← hkE]
    show E (M₀ z) = 1
    rw [hM₀, (hke z).2 hz, MonObj.one_comp]
  · have : (d : ℂ) • H.symm z = M₁ z := by
      show (d : ℂ) • ((d : ℂ)⁻¹ • M₁ z) = M₁ z
      rw [smul_smul, mul_inv_cancel₀ hd', one_smul]
    rw [this, ← hke, hM₁, (hkE z).2 hz, MonObj.one_comp]

theorem UpperTheory.Gal.W2.isogAt_of :
    UpperTheory.Gal.W2.TateWit → UpperTheory.Gal.W2.PerLin → UpperTheory.Gal.W2.IsogAt := by
  intro hTW hPL p _ D G L gb N N' h hLev X X' c hX hL hX' hL' ρ hF D' t P x e hU
  obtain ⟨hN3, hNp, hN'3, hN'p, -, -⟩ := hLev
  have hN : 0 < N := by omega
  have hN' : 0 < N' := by omega
  obtain ⟨hmon, hact, ⟨ψ', d, hmon', -, hψψ', hψ'ψ, hdp⟩, hTate⟩ := c.tr
  haveI := hmon
  haveI := hmon'
  have hd : d ≠ 0 := by
    rintro rfl
    have := (Fact.out : p.Prime).one_lt
    simp only [Nat.coprime_zero_left] at hdp
    omega
  have hys : (x ≫ c.q) ≫ X.s = spMap (RingHom.id ℂ) := by
    rw [Category.assoc, c.ov]
    exact hU.1
  have hpts : ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P₁ : D''.La →+ (Fin D.g → ℂ))
      (E : (Fin D.g → ℂ) → (Over.mk (x ≫ c.q) ⟶ X.univ.A)), D.Cls N D'' t'' ∧
        UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P₁ (x ≫ c.q) E := hF.pts (x ≫ c.q) hys
  obtain ⟨D'', t'', P₁, E, hC, hE⟩ := hpts
  have hO : SmoothOfRelativeDimension D.g c.o.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.g).of_isPullback c.φ.cart.1 hX
  have hPo' : c.o.P.IsLB := c.o.isLB
  have hPM : X.univ.P.IsLB := X.univ.isLB
  have hLo : (c.o.P.pull (lift (𝟙 c.o.A) (𝟙 c.o.A)).left).IsLB := pull_isLB hPo' _
  have isoB : LBIso (c.o.P.pull (lift (𝟙 c.o.A) (𝟙 c.o.A)).left)
      ((X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).pull c.φ.φ) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hPo' _) (pull_isLB (pull_isLB hPM _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_pull hPo', (GlobalTheory.CechPic.cls_eq_iff hPo' (pull_isLB hPM _)).2 c.φ.pol, GlobalTheory.CechPic.cls_pull hPM,
      ← GlobalTheory.CechPic.pull_comp, GlobalTheory.DiagAmpleBC.diag_comp X.univ.A c.o.A c.φ.φ c.φ.φ₂ c.φ.sq, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.cls_pull (pull_isLB hPM _), GlobalTheory.CechPic.cls_pull hPM]
  obtain ⟨E', hE', hEE'⟩ := (GlobalTheory.unifAt_correspond_of_cartesian D.O D.inv D.g ρ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) D.La
    (gfam X.univ hX hL) (gfam c.o hO hLo) N c.q c.φ.φ c.φ.cart c.φ.act isoB c.φ.eta D'' t'' P₁ x hU.1 hys).2 E hE
  obtain ⟨H, hEH, hHmem, hHmem'⟩ := exists_linearEquiv_of_isog D.g X'.univ.ab hX' c.o.ab hO x e E' hU.2.2.1 hE'.2.2.1
    P.range P₁.range hU.2.1.2.2.1 hE'.2.1.2.2.1 hU.2.2.2.1 hE'.2.2.2.1 c.ψ ψ' d hd hψψ' hψ'ψ
  have hHρ : ∀ (a : D.O) z, H (ρ a *ᵥ z) = ρ a *ᵥ H z := by
    intro a z
    have := lin_eq_of_exp E' P₁.range hE'.2.1.2.2.1 hE'.2.2.1.1 hE'.2.2.2.1
      ((H : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)) ∘ₗ Matrix.mulVecLin (ρ a))
      (Matrix.mulVecLin (ρ a) ∘ₗ (H : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ))) (fun z => by
        show E' (H (ρ a *ᵥ z)) = E' (ρ a *ᵥ H z)
        have e1 : E' (ρ a *ᵥ H z) = E' (H z) ≫ c.o.act.act a := hE'.2.2.2.2.1 a (H z)
        have e2 : e (ρ a *ᵥ z) = e z ≫ X'.univ.act.act a := hU.2.2.2.2.1 a z
        rw [hEH, e1, hEH, e2]
        exact (Category.assoc _ _ _).trans ((congrArg (fun u => e z ≫ u) (hact a)).trans (Category.assoc _ _ _).symm))
    exact LinearMap.congr_fun this z
  have hHρ' : ∀ (a : D.O) z, H.symm (ρ a *ᵥ z) = ρ a *ᵥ H.symm z := by
    intro a z
    apply H.injective
    rw [hHρ, H.apply_symm_apply, H.apply_symm_apply]
  let P'' : D''.La →+ (Fin D.g → ℂ) := (H.symm : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)).toAddMonoidHom.comp P₁
  have hP'' : ∀ u, P'' u = H.symm (P₁ u) := fun u => rfl
  have hmat : ∀ z, LinearMap.toMatrix' (H.symm : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)) *ᵥ z = H.symm z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  have hper'' : IsPeriod D'' ρ P'' := hPL D.O D.inv D.g ρ D'' P₁ P''
    (LinearMap.toMatrix' (H.symm : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ))) hE'.2.1
    (by
      rw [LinearMap.det_toMatrix']
      exact (LinearEquiv.isUnit_det' H.symm).ne_zero)
    (fun a => Matrix.toLin'.injective (LinearMap.ext fun z => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmat, hmat, hHρ']))
    (fun u => (hmat _).symm)
  have hmark : IsMarkedIsom N D'' D'' t'' t'' (LinearEquiv.refl D.O D''.La) :=
    ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩
  have hE2 : UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) (fun z => E (H z)) :=
    _root_.GlobalTheory.PELU.unifAt_transport D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam X.univ hX hL) N D'' D'' t'' t'' P₁ P'' (x ≫ c.q) E
      (LinearEquiv.refl D.O D''.La) H.symm hN hE hmark (fun _ => rfl) hper''
  have hE3 : UnifAt (gfam c.o hO hLo) (RingHom.id ℂ) ρ N D'' t'' P'' x (fun z => E' (H z)) :=
    _root_.GlobalTheory.PELU.unifAt_transport D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam c.o hO hLo) N D'' D'' t'' t'' P₁ P'' x E'
      (LinearEquiv.refl D.O D''.La) H.symm hN hE' hmark (fun _ => rfl) hper''
  have hι : ∀ u, ∃ v, P₁ v = H (P u) := by
    intro u
    exact hHmem (P u) ⟨u, rfl⟩
  choose fι hfι using hι
  have hPf : ∀ u, P'' (fι u) = P u := fun u => by
    rw [hP'', hfι, H.symm_apply_apply]
  have hinj'' : Function.Injective P'' := hper''.2.1
  let inc : D'.La →ₗ[D.O] D''.La :=
    { toFun := fι
      map_add' := fun u v => hinj'' (by rw [map_add (f := _), hPf, hPf, hPf, map_add (f := _)])
      map_smul' := fun a u => hinj'' (by rw [RingHom.id_apply, hper''.1, hPf, hPf]; exact hU.2.1.1 a u) }
  have hPinc : ∀ u, P'' (inc u) = P u := hPf
  obtain ⟨I', I'', hI', hI'', hT⟩ := hTate ℂ x (RingHom.id ℂ) hU.1
  obtain ⟨f, nu, hw, hfN, hfe⟩ := hTW p D gb N' X'.X X'.s X'.univ hX' hL' ρ D' t P x e hN' hN'p hU I' hI'
  obtain ⟨f'', nu'', hw'', hfN'', hfe''⟩ := hTW p D gb N X'.X X'.s c.o hO hLo ρ D'' t'' P'' x _ hN hNp hE3 I'' hI''
  refine ⟨D'', t'', P'', fun z => E (H z), inc, d, hC, hE2, hPinc, fun z => ?_, hdp, fun u'' => ?_,
    f, nu, f'', nu'', hw, hw'', hfN, hfN'', fun n hn hnp a b => ?_⟩
  · show (E (H z)).left = (e z).left ≫ c.ψ.left ≫ c.φ.φ
    rw [hEE' (H z), hEH z]
    exact Category.assoc _ _ _
  · obtain ⟨u, hu⟩ := hHmem' (P₁ u'') ⟨u'', rfl⟩
    refine ⟨u, hinj'' ?_⟩
    rw [hPinc, hu, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
    rfl
  · rw [← hT n hn hnp a b]
    have h1 : I'.ev n a ≫ c.ψ = E' (H ((n : ℂ)⁻¹ • P'' (inc (f n a)))) := by
      rw [hfe n hn hnp a, hPinc, hEH]
    rw [h1, hfe'' n hn hnp b]
    exact (GlobalTheory.UPel.HT.unifCls_eq_iff (fun z => E' (H z)) P'' hE3.2.2.1.1 hE3.2.2.2.1 hinj'' hn _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PJLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma hv_sub_l {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) :
    hv M (x - y) z = hv M x z - hv M y z := by
  unfold hv
  rw [Matrix.mulVec_sub, dotProduct_sub]

private lemma hv_smul_l {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x z : Fin n → ℂ) :
    hv M (c • x) z = c * hv M x z := by
  unfold hv
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma hv_smul_r {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x z : Fin n → ℂ) :
    hv M x (c • z) = star c * hv M x z := by
  unfold hv
  rw [star_smul, smul_dotProduct, smul_eq_mul]

private lemma hv_J {n : ℕ} {M J : Matrix (Fin n) (Fin n) ℂ} (h : Jᴴ * M * J = M) (x y : Fin n → ℂ) :
    hv M (J *ᵥ x) (J *ᵥ y) = hv M x y := by
  unfold hv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h]

private lemma J_plus {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {t : ℂ} (ht : t * t = -1)
    (hJ : J * J = -1) (x : Fin n → ℂ) :
    J *ᵥ (x - t • J *ᵥ x) = t • (x - t • J *ᵥ x) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (J *ᵥ x) i * ht

private lemma of_plus_zero {n : ℕ} {t : ℂ} (ht : t * t = -1) {x y : Fin n → ℂ}
    (h : x - t • y = 0) : y = (-t) • x := by
  have hx : x = t • y := sub_eq_zero.mp h
  rw [hx, smul_smul, neg_mul, ht, neg_neg, one_smul]

private lemma eig_pos {n : ℕ} {M J : Matrix (Fin n) (Fin n) ℂ} {t : ℂ} (ht : t * t = -1)
    (hp : ∀ x, x ≠ 0 → 0 < (-t * hv M (J *ᵥ x) x).re) {z : Fin n → ℂ} (hz : z ≠ 0)
    (hJz : J *ᵥ z = t • z) : 0 < (hv M z z).re := by
  have h1 := hp z hz
  rw [hJz, hv_smul_l, ← _root_.mul_assoc, neg_mul, ht, neg_neg, _root_.one_mul] at h1
  exact h1

private lemma core {n : ℕ} (M J : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) (ht : t * t = -1)
    (hJ : J * J = -1) (hP : Jᴴ * M * J = M)
    (hp : ∀ x, x ≠ 0 → 0 < (-t * hv M (J *ᵥ x) x).re) :
    (∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = t • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = t • z →
      ∀ x, J *ᵥ x = t • ((2 * (hv M x z / hv M z z)) • z - x) := by
  have hpos : ∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re := fun z hz hJz => eig_pos ht hp hz hJz
  have hall : (∀ x, x - t • J *ᵥ x = 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro h0
    have hx : ∀ x, J *ᵥ x = (-t) • x := fun x => of_plus_zero ht (h0 x)
    apply Matrix.ext_of_mulVec_single
    intro i
    simp only [hx]
    ext k
    by_cases h : k = i
    · subst h
      simp [Pi.single_apply, Matrix.one_apply]
    · simp [Pi.single_apply, Matrix.one_apply, h]
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro hneg
    apply hall
    intro x
    by_contra hv0
    have h1 := hpos _ hv0 (J_plus ht hJ x)
    have h2 := hneg _ hv0
    linarith
  · rintro ⟨z, hz⟩
    by_contra hno
    push_neg at hno
    have h0 : ∀ x, x - t • J *ᵥ x = 0 := by
      intro x
      by_contra hv0
      exact hno _ hv0 (J_plus ht hJ x)
    have hx : ∀ x, J *ᵥ x = (-t) • x := fun x => of_plus_zero ht (h0 x)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [hv] at hz
    have h1 := hp z hz0
    rw [hx, hv_smul_l, ← _root_.mul_assoc, neg_mul_neg, ht, neg_one_mul, Complex.neg_re] at h1
    linarith
  · intro z hz hperp hJz x
    have hzz : hv M z z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
    set c := hv M x z / hv M z z with hc
    set w := x - c • z with hw
    have hwz : hv M w z = 0 := by
      rw [hw, hv_sub_l, hv_smul_l, hc, div_mul_cancel₀ _ hzz, sub_self]
    have hJwz : hv M (J *ᵥ w) z = 0 := by
      have e1 := hv_J hP w z
      rw [hJz, hv_smul_r, hwz] at e1
      have ht0 : star t ≠ 0 := by
        intro h0
        rw [star_eq_zero] at h0
        rw [h0, zero_mul] at ht
        norm_num at ht
      exact (mul_eq_zero.mp e1).resolve_left ht0
    have hJw : J *ᵥ w = (-t) • w := by
      apply of_plus_zero ht
      by_contra hu
      have h1 := hpos _ hu (J_plus ht hJ w)
      have h2 := hperp _ hu (by rw [hv_sub_l, hv_smul_l, hwz, hJwz, mul_zero, sub_zero])
      linarith
    have hxw : x = w + c • z := by rw [hw, sub_add_cancel]
    rw [hxw, Matrix.mulVec_add, hJw, Matrix.mulVec_smul, hJz]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

theorem UpperTheory.Gal.W2.jLine_of :
    UpperTheory.Gal.W2.JLine := by
  intro n M J s hM hs hPJ
  obtain ⟨hJ, hP, hp⟩ := hPJ
  have ht : (s * Complex.I) * (s * Complex.I) = -1 := by
    rcases hs with rfl | rfl <;> simp
  have hp' : ∀ x, x ≠ 0 → 0 < (-(s * Complex.I) * hv M (J *ᵥ x) x).re := by
    intro x hx
    have h1 := hp x hx
    rwa [neg_mul] at h1
  exact core M J (s * Complex.I) ht hJ hP hp'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLineBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem one_add_col_mul_rank_one_mulVec {n : ℕ} (u w v : Fin n → ℂ) :
    (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit w) *ᵥ v = v + (w ⬝ᵥ v) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

private theorem hv_sub_smul_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) (a : ℂ) :
    hv M (x - a • y) z = hv M x z - a * hv M y z := by
  simp [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]

theorem UpperTheory.Gal.W2.lineBasis_of :
    UpperTheory.Gal.W2.LineBasis := by
  intro n M z _ hpos
  have hz : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    have : z = 0 := funext h
    subst this
    simp [hv] at hpos
  obtain ⟨i₀, hi₀⟩ := hz
  have hφ : hv M z z ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  set e : Fin n → ℂ := Pi.single i₀ 1 with he
  set c : Fin n → ℂ := fun j => if j = i₀ then 0 else hv M (Pi.single j 1) z / hv M z z with hc
  refine ⟨i₀, (1 + Matrix.replicateCol Unit (z - e) * Matrix.replicateRow Unit e) *
    (1 + Matrix.replicateCol Unit (-e) * Matrix.replicateRow Unit c), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    have h1 : e ⬝ᵥ (z - e) = z i₀ - 1 := by
      simp [he, dotProduct_sub]
    have h2 : c ⬝ᵥ (-e) = 0 := by
      simp [he, hc]
    rw [h1, h2]
    simpa using hi₀
  · rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ e = 0 := by simp [he, hc]
    have h3 : e ⬝ᵥ e = 1 := by simp [he]
    rw [h2]
    simp [h3, he]
  · intro i hi
    rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ (Pi.single i 1 : Fin n → ℂ) = hv M (Pi.single i 1) z / hv M z z := by
      simp [hc, hi]
    have h3 : e ⬝ᵥ ((Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e)) =
        - (hv M (Pi.single i 1) z / hv M z z) := by
      simp [he, dotProduct_add, Pi.single_apply, hi]
    rw [h2, h3]
    have h4 : (Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e) +
        (-(hv M (Pi.single i 1) z / hv M z z)) • (z - e) =
        (Pi.single i 1 : Fin n → ℂ) - (hv M (Pi.single i 1) z / hv M z z) • z := by
      ext a
      simp
      ring
    rw [h4, hv_sub_smul_left]
    field_simp
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.POneAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem congOne_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') {g : G.GAf} (h : L.CongOne N' g) : L.CongOne N g := by
  obtain ⟨k, rfl⟩ := hd
  intro v hv
  obtain ⟨w, hw, hv'⟩ := h v hv
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [hv', smul_smul]⟩

private theorem coordA_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.oneAt_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.OneAt := by
  intro hk li p _ D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hF B PD D' t hcls j a hpl hco hloc P x e hU
  obtain ⟨h3, hcop, h3', hcop', hdvd, -⟩ := hlev
  have lev1 : LevOk L N N' 1 := ⟨h3, hcop, h3', hcop', hdvd, fun u hu => by
    have hm : u ∈ L.KN N := ⟨congOne_of_dvd L hdvd hu.1, congOne_of_dvd L hdvd hu.2⟩
    simpa using hm⟩
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hPinc, he'', -, hj'', hpl'', hco'', hloc''⟩ :=
    hk p D G L gb N N' 1 lev1 X X' c₁ hX hL hX' hL' ρ hF D' t P x e hU B j a.1 (PD.lat a.2) hpl hco hloc
  have hco₁ : IsCoordA L (trivX B) N D'' t'' j'' a.1 := by simpa using hco''
  have hpos : 0 < N := by omega
  obtain ⟨w, hmk, hw⟩ := (li p D G L B PD N hpos hcop D' t D'' t'' j j'' a a N' N t t'' hcls hcls'' hpl hpl''
    (coordA_of_dvd L hdvd hco) hco₁ hloc hloc'' 1).1 ⟨by simp, by simp⟩
  have hw1 : ∀ u, j (w u) = j'' u := fun u => by
    rw [hw u]
    simp [actY]
  have hinc : ∀ u, w (inc u) = u := fun u => hpl.1 (by rw [hw1, hj''])
  have hP : ∀ u'', P (w u'') = P'' u'' := fun u'' => by
    have e1 : inc (w u'') = u'' := w.injective (hinc _)
    rw [← hPinc, e1]
  refine ⟨_, _root_.GlobalTheory.PELU.unifAt_transport D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam X.univ hX hL) N D'' D' t'' t P'' P
    (x ≫ c₁.q) e'' w (LinearEquiv.refl ℂ _) hpos hU'' hmk (fun u => hP u) hU.2.1, fun z => ?_⟩
  simpa using he'' z
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceT
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_not_real {tr nm : ℤ} {r : ℂ} (hd : tr ^ 2 - 4 * nm < 0)
    (hr : r ^ 2 - (tr : ℂ) * r + (nm : ℂ) = 0) : (starRingEnd ℂ) r ≠ r := by
  intro hc
  have him : r.im = 0 := Complex.conj_eq_iff_im.mp hc
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩
  have h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0 := by exact_mod_cast hr
  have h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * x - (tr : ℝ))]

theorem UpperTheory.Gal.W2.placeT_of :
    UpperTheory.Gal.W2.PlaceT := by
  intro p _ D G L ha v hv t₀ ht
  have i₀ : Fin D.a := ⟨0, by omega⟩
  have hsub : ∀ i j : Fin D.a, i = j := fun i j => by
    apply Fin.ext; have := i.2; have := j.2; omega
  have hρ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  have hne : (starRingEnd ℂ) D.ρc ≠ D.ρc := rho_not_real D.disc_neg D.ρc_root
  obtain ⟨i, hi⟩ := (L.sig v).1 hv
  have hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x := fun x => by
    rw [← ht i]; exact L.s_C i x
  refine ⟨fun v' hv' => ?_, hρ, hne, ?_⟩
  · obtain ⟨j, hj⟩ := (L.sig v').1 hv'
    rw [hi, hj, hsub i j]
  · have hemb := InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))
    rw [← hi] at hemb
    rcases hemb with h | h
    · left
      have hx : ∀ x, v.embedding (L.e x) = t₀ x := fun x => by rw [h]; exact hφ x
      refine ⟨?_, hx⟩
      unfold sgnV
      rw [if_pos (by rw [hx, hρ])]
    · right
      have hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x) := fun x => by
        rw [h, ComplexEmbedding.conjugate_coe_eq, hφ]
      have hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc := by rw [hx, hρ]; exact hne
      refine ⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩
      unfold sgnV
      rw [if_neg hω]
end

