module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0059

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExistsCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_coords {K C V : Type} [Field K] [Ring C] [Algebra K C] [Algebra ℚ K] [Algebra ℚ C]
    [IsScalarTower ℚ K C] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [FiniteDimensional ℚ K]
    [FiniteDimensional K C] (n : ℕ)
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hinj : Function.Injective rep) (hC : Module.finrank K C = n ^ 2)
    (hdim : Module.finrank ℚ V = n * Module.finrank ℚ K) :
    ∃ (kp : V ≃+ (Fin n → K)) (σ : C ≃ₐ[K] Matrix (Fin n) (Fin n) K), ∀ c w, kp (rep c w) = σ c *ᵥ kp w := by
  let f : K →+* Module.End ℚ V := (rep : C →+* Module.End ℚ V).comp (algebraMap K C)
  letI : Module K V := Module.compHom V f
  have hsm : ∀ (x : K) (w : V), x • w = rep (algebraMap K C x) w := fun _ _ => rfl
  haveI : IsScalarTower ℚ K V := by
    refine ⟨fun q x w => ?_⟩
    rw [hsm, hsm, ← IsScalarTower.toAlgHom_apply ℚ K C, map_smul, map_smul]
    rfl
  haveI : Module.Finite K V := Module.Finite.of_restrictScalars_finite ℚ K V
  have hfin : Module.finrank K V = n := by
    have h := Module.finrank_mul_finrank ℚ K V
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hdim, mul_comm n] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  let b : Module.Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hfin
  let r : C →ₐ[K] Module.End K V := AlgHom.ofLinearMap
    { toFun := fun c =>
        { toFun := rep c
          map_add' := map_add _
          map_smul' := fun x w => by
            simp only [RingHom.id_apply, hsm]
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes] }
      map_add' := fun c c' => by ext w; simp
      map_smul' := fun x c => by
        ext w
        simp [hsm, Algebra.smul_def, Module.End.mul_apply] }
    (by ext w; simp) (fun c c' => by ext w; simp [Module.End.mul_apply])
  have hr : ∀ c w, r c w = rep c w := fun _ _ => rfl
  let s : C →ₐ[K] Matrix (Fin n) (Fin n) K := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp r
  have hsinj : Function.Injective s := by
    intro c c' h
    have h' : r c = r c' := (LinearMap.toMatrixAlgEquiv b).injective h
    apply hinj
    ext w
    exact congrArg (fun g => g w) h'
  have hrk : Module.finrank K C = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [hC, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
    ring
  have hsurj : Function.Surjective s :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := s.toLinearMap) hrk).1 hsinj
  refine ⟨b.equivFun.toAddEquiv, AlgEquiv.ofBijective s ⟨hsinj, hsurj⟩, fun c w => ?_⟩
  have h := LinearMap.toMatrix_mulVec_repr b b (r c) w
  exact h.symm

theorem UpperTheory.Gal.W2.fMat_of :
    UpperTheory.Gal.W2.FMat := by
  intro p _ D G L hm
  haveI := D.freeLa
  haveI := D.finLa
  have hK : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    ((AlgEquiv.ofRingEquiv (f := L.e) (fun q => map_ratCast L.e q)).toLinearEquiv.finrank_eq).symm
  have hdim : Module.finrank ℚ (VQ D) = G.n * Module.finrank ℚ G.F := by
    rw [Module.finrank_baseChange, D.rankLa, hm, Nat.one_mul, L.n_eq, hK]
  exact exists_coords G.n L.rep L.rep_inj G.rankC hdim
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExistsPosForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_pos_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h1 : sigPosH hA = 1) :
    ∃ w : Fin n → ℂ, 0 < (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hne : Nonempty {i : Fin n // 0 < hA.eigenvalues i} := by
    apply Fintype.card_pos_iff.1
    unfold sigPosH at h1
    omega
  obtain ⟨i, hi⟩ := hne
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1, ?_⟩
  rw [GlobalTheory.SignatureOneForms.form_re_eq_sum hA]
  have hU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ
      ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  rw [hU, Finset.sum_eq_single i]
  · simpa using hi
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem UpperTheory.Gal.W2.sigB_of :
    UpperTheory.Gal.W2.SigB := by
  intro p _ G B v
  obtain ⟨hH, hdet, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v B.β B.sym B.trivR
  have hZi : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiZ : ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x y : Fin G.n → ℂ, hv (GlobalTheory.LKCx.herm G v B.β) x y =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) ⬝ᵥ
        (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x)) := by
    intro x y
    unfold hv
    rw [hZ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hinj : ∀ x : Fin G.n → ℂ, x ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x ≠ 0 := by
    intro x hx h0
    apply hx
    have h2 := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec, hiZ] using h2
  refine ⟨hH, fun h1 => ⟨?_, ?_⟩, fun h1 => ?_⟩
  · obtain ⟨w, hw⟩ := exists_pos_form (G.gram_herm v) h1
    refine ⟨((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w, ?_⟩
    rw [key, Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
    exact hw
  · intro z x hz hx hxz
    rw [key] at hz hxz ⊢
    exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _ hz hxz (hinj x hx)
  · have h0 : sigPosH (G.gram_herm v) = 0 := by
      rcases G.sig v with h | h
      · exact absurd h.1 h1
      · exact h.1
    intro x hx
    rw [key]
    exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (hinj x hx)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixedPointsIntegralBaseOfUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem kn_anti {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') : L.KN N' ≤ L.KN N := by
  obtain ⟨k, rfl⟩ := hd
  intro u hu
  have hu' : L.CongOne (N * k) u ∧ L.CongOne (N * k) u⁻¹ := hu
  show L.CongOne N u ∧ L.CongOne N u⁻¹
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨w, hw, e⟩ := hu'.1 v hv
    exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩
  · obtain ⟨w, hw, e⟩ := hu'.2 v hv
    exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

private theorem s_inv {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ} {h : G.GAf}
    (hd : N ∣ N') (hc : ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N) :
    ∀ u ∈ L.KN N', ∀ g, u⁻¹ * g * u ∈ {g | h * g ∈ L.KN N} ↔ g ∈ {g | h * g ∈ L.KN N} := by
  intro u hu g
  have a : h * u⁻¹ * h⁻¹ ∈ L.KN N := hc _ (inv_mem hu)
  have b : u ∈ L.KN N := kn_anti L hd hu
  have e : h * (u⁻¹ * g * u) = (h * u⁻¹ * h⁻¹) * (h * g) * u := by group
  show h * (u⁻¹ * g * u) ∈ L.KN N ↔ h * g ∈ L.KN N
  rw [e, Subgroup.mul_mem_cancel_right _ b, Subgroup.mul_mem_cancel_left _ a]

private theorem sees_div {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (a : GlobalTheory.LKCx.Dat G v B.β) (K : Subgroup G.GAf) (h : G.GAf) (y y' : GlobalTheory.LKCx.grp G B.β)
    (H : Sees B {g | h * g ∈ K} a y) (H' : Sees B {g | h * g ∈ K} a y') : Sees B (K : Set G.GAf) a (y⁻¹ * y') := by
  obtain ⟨⟨c, hc⟩, hS, hK⟩ := H
  obtain ⟨⟨c', hc'⟩, hS', hK'⟩ := H'
  have hS1 : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ K := hS
  have hS2 : h * (a.1.1⁻¹ * B.toAf y' * a.1.1) ∈ K := hS'
  refine ⟨⟨c⁻¹ * c', ?_⟩, ?_, ?_⟩
  · have key : ∀ w : Fin G.n → ℂ,
        ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ ((LKCx.toV G v B.β y).val *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [map_mul, map_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]
    by_cases h0 : c = 0
    · have hz := key a.2.1
      rw [hc, h0, zero_smul, Matrix.mulVec_zero] at hz
      rw [← hz]
      simp
    · have hz := key a.2.1
      rw [hc, Matrix.mulVec_smul] at hz
      have h3 : ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1 = c⁻¹ • a.2.1 := by
        calc _ = c⁻¹ • (c • (((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1)) := by
                rw [smul_smul, _root_.inv_mul_cancel₀ h0, one_smul]
          _ = _ := by rw [hz]
      rw [h3, smul_smul, _root_.mul_comm]
  · show a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 ∈ K
    have e : a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 =
        (h * (a.1.1⁻¹ * B.toAf y * a.1.1))⁻¹ * (h * (a.1.1⁻¹ * B.toAf y' * a.1.1)) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact K.mul_mem (K.inv_mem hS1) hS2
  · have e : a.1.2⁻¹ * LKCx.toP1 G B.β (y⁻¹ * y') * a.1.2 =
        (a.1.2⁻¹ * LKCx.toP1 G B.β y * a.1.2)⁻¹ * (a.1.2⁻¹ * LKCx.toP1 G B.β y' * a.1.2) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hK) hK'

theorem UpperTheory.Gal.W2.fixedPoints_integral_base_of_uniformisation :
    UpperTheory.Gal.W2.RhoSig → UpperTheory.Gal.W2.GUnif → UpperTheory.Gal.W2.PDicEx → UpperTheory.Gal.W2.RDicEx → UpperTheory.Gal.W2.UnifG → UpperTheory.Gal.W2.StabTriv → UpperTheory.Gal.W2.FixFwd → UpperTheory.Gal.W2.FixEq → UpperTheory.Gal.W2.FixGa → UpperTheory.Gal.W2.FixLoc → UpperTheory.Gal.W2.TanExists → UpperTheory.Gal.W2.FixFinite → UpperTheory.Gal.W2.PowSm → UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.SumPts → UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.HeckeFixedPointCMCycleClass := by
  intro hRS hGU hPDE hRDE hUG hST hFF hFE hFG hFLo hTE hFFin hPS hPO hSP hES
  intro p _ D G L ha hm v hs t₀ ht gb hstd N N' h hlev X X' c₁ c₂ hreg k α hα het h₁ h₂
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨ρ, hsig⟩ := hRS p D ha hm t₀ ht
  obtain ⟨hsm, hqc, hsep, hX, hL, hfine, ⟨U₀⟩⟩ := hGU p D ha hm t₀ ht ρ hsig gb hstd N h3 hcp X
  obtain ⟨hsm', hqc', hsep', hX', hL', hfine', ⟨U⟩⟩ := hGU p D ha hm t₀ ht ρ hsig gb hstd N' h3' hcp' X'
  have hpow := @hPS X.X X.s (D.n - 1) D.g hsm hqc hsep X.univ.A X.univ.grp X.univ.comm X.univ.ab hX k
  have hpow' := @hPS X'.X X'.s (D.n - 1) D.g hsm' hqc' hsep' X'.univ.A X'.univ.grp X'.univ.comm X'.univ.ab hX' k
  refine ⟨hpow.1, ?_⟩
  have hTan : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α →
      ∃ A, W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x A :=
    fun x hx => hTE _ _ (sZ X k) (sZ X' k) _ hpow.1 (c₁.pw k) (c₂.tw α) h₁ h₂ het x hx
  let At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ :=
    fun x => if hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α then (hTan x hx).choose else 0
  have hAt : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), ∀ hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α,
      W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) := by
    intro x hx
    simp only [At, dif_pos hx]
    exact (hTan x hx).choose_spec
  let PD : (B : LKCx.Form G) → PDic L B.β := fun B => (hPDE p D G L ha hm B).some
  let RD : (B : LKCx.Form G) → RDic L v B.β ρ t₀ := fun B => (hRDE p D G L ha hm v hs t₀ ht ρ hsig B).some
  obtain ⟨Φ, hΦ⟩ := hUG p D G L ha hm v hs t₀ ht ρ hsig PD RD N' (by omega) hcp' _ U
  have hproj : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ),
      (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ X'.s = spMap (RingHom.id ℂ) := by
    intro x
    rw [Category.assoc]
    exact x.2
  let π : CxPts (sZ X' k) (RingHom.id ℂ) → CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) :=
    fun x => ⟨x.1 ≫ (KS.pow X'.univ.A k).hom, hproj x⟩
  have hbase : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α →
      (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₁.q = (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₂.q := by
    intro x hx
    rw [Category.assoc, Category.assoc, ← (hPO p D G L gb N N' 1 X X' c₁ k).1,
      ← ((hPO p D G L gb N N' h X X' c₂ k).2.2.2 α).1, ← Category.assoc, ← Category.assoc, hx]
  have hFwd : ∀ (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j,
      PELU.IsPeriod (U.Di i) ρ P →
      IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a →
      U.u i P ≫ c₁.q = U.u i P ≫ c₂.q → ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y :=
    fun q a i P j hper hco hfb => hFF p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ
      hfine v t₀ (Quot.out q) (PD _) (RD _) (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P)
      (U.unif i P hper) hfb
  have hLoc := fun (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j
      (hper : PELU.IsPeriod (U.Di i) ρ P)
      (hco : IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a)
      (y : LKCx.grp G (Quot.out q).β) (hy : Sees (Quot.out q) {g | h * g ∈ L.KN N} a y) =>
    hFLo p D G L ha hm v hs t₀ ht gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig
      hsm' hreg U (Quot.out q) (PD _) (RD _) i P j a hper hco y hy k α hα h₁ h₂
  have hdet : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α → (1 - At x).det ≠ 0 := by
    intro x hx
    obtain ⟨q, a, i, P, j, -, hper, hxu, hco⟩ := hΦ (π x)
    have hxu' : x.1 ≫ (KS.pow X'.univ.A k).hom = U.u i P := hxu
    have hfb : U.u i P ≫ c₁.q = U.u i P ≫ c₂.q := by rw [← hxu']; exact hbase x hx
    obtain ⟨y, hy⟩ := hFwd q a i P j hper hco hfb
    obtain ⟨Fl, hFl, -, hAll⟩ := hLoc q a i P j hper hco y hy
    exact (hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).1 x ((hFl x).2 ⟨hxu', hx⟩)
  have hfin : {x : CxPts (sZ X' k) (RingHom.id ℂ) | x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α}.Finite :=
    hFFin _ _ (sZ X k) (sZ X' k) (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ hpow.2.2.1 hpow'.2.1 hpow'.2.2.2
      (fun x hx => ⟨At x, hAt x hx, hdet x hx⟩)
  have hSinv := s_inv L hd hconj
  have hK1 : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y : LKCx.grp G B.β),
      Sees B (L.KN N' : Set G.GAf) a y → y = 1 :=
    fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N' h3' hcp' B a y hy
  have huniq : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y y' : LKCx.grp G B.β),
      Sees B {g | h * g ∈ L.KN N} a y → Sees B {g | h * g ∈ L.KN N} a y' → y = y' := by
    intro B a y y' hy hy'
    exact _root_.inv_mul_eq_one.1
      (hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a _ (sees_div B a (L.KN N) h y y' hy hy'))
  have hFb : ∀ (x' : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ)) (q : LKCx.FCls G)
      (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j,
      PELU.IsPeriod (U.Di i) ρ P → x'.1 = U.u i P →
      IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a →
      (x' ∈ hfin.toFinset.image π ↔ ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y) := by
    intro x' q a i P j hper hxu hco
    constructor
    · intro hx'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      have hx2 : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α := hfin.mem_toFinset.1 hx
      apply hFwd q a i P j hper hco
      rw [← hxu]
      exact hbase x hx2
    · rintro ⟨y, hy⟩
      obtain ⟨Fl, hFl, ⟨x, hxF⟩, -⟩ := hLoc q a i P j hper hco y hy
      obtain ⟨hxu', hx2⟩ := (hFl x).1 hxF
      exact Finset.mem_image.2 ⟨x, hfin.mem_toFinset.2 hx2, Subtype.ext (hxu'.trans hxu.symm)⟩
  refine ⟨hfin.toFinset, At, fun x => by rw [Set.Finite.mem_toFinset]; rfl,
    fun x hx => ⟨hAt x (hfin.mem_toFinset.1 hx), hdet x (hfin.mem_toFinset.1 hx)⟩, ?_,
    fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a y hy, fun t => ?_⟩
  · refine ((hfin.toFinset.image π).finite_toSet.image Φ).subset ?_
    intro z hz
    obtain ⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩ := hΦ (Φ.symm z)
    rw [Equiv.apply_symm_apply] at hΦx
    subst hΦx
    refine ⟨Φ.symm _, ?_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨y, hy⟩ := hz
    obtain ⟨E, -, hE⟩ := hES p G v (fun _ _ => 0) (Quot.out q) (L.KN N') {g | h * g ∈ L.KN N} hSinv _ a
      (Quot.out_eq _)
    exact (hFb _ q a i P j hper hxu hco).2 ⟨E y, (hE y).1.1 hy⟩
  · let w : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) → ℂ :=
      fun x' => ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t
    have hsum : ∑ x ∈ hfin.toFinset, lefTerm (At x) t = ∑ x' ∈ hfin.toFinset.image π, w x' :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) _).symm
    rw [hsum]
    refine hSP p G v (wtFix L v t₀ α t) (L.KN N') {g | h * g ∈ L.KN N} hSinv hK1 huniq _ Φ _ w (fun x' => ?_)
    obtain ⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩ := hΦ x'
    refine ⟨q, a, hΦx, hFb x' q a i P j hper hxu hco, fun y hy => ?_⟩
    obtain ⟨Fl, hFl, -, hAll⟩ := hLoc q a i P j hper hco y hy
    have hEq : hfin.toFinset.filter (fun x => π x = x') = Fl := by
      ext x
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hFl x]
      constructor
      · rintro ⟨hx, he⟩
        refine ⟨?_, hx⟩
        rw [← hxu, ← he]
        rfl
      · rintro ⟨he, hx⟩
        exact ⟨hx, Subtype.ext (he.trans hxu.symm)⟩
    show ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t = _
    rw [hEq]
    exact (hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).2 t
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PArchSpan
section
noncomputable section

open NumberField

namespace UpperTheory.Gal.W2

private theorem two_mul_card_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] :
    2 * Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero F]
  ring

open scoped Classical in
private theorem sum_fibre_place (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F)
    (v : InfinitePlace F) :
    ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x = ((2 * (v.embedding x).re : ℝ) : ℂ) :=
  _root_.UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place F x v

private theorem trace_eq_sum_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
    rw [eq_ratCast] at h
    let e : (F →ₐ[ℚ] ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun σ => σ.toRingHom
        invFun := fun φ => φ.toRatAlgHom
        left_inv := fun σ => by ext a; rfl
        right_inv := fun φ => by ext a; rfl }
    exact h.trans (Fintype.sum_equiv e _ _ fun _ => rfl)
  have h2 : ∑ φ : F →+* ℂ, φ x =
      ∑ v : InfinitePlace F, ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x :=
    (Finset.sum_fiberwise _ _ _).symm
  have h3 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((∑ v : InfinitePlace F, 2 * (v.embedding x).re : ℝ) : ℂ) := by
    rw [h1, h2, Finset.sum_congr rfl fun v _ => sum_fibre_place F x v, Complex.ofReal_sum]
  have h4 : (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
    push_cast
    rfl
  exact Complex.ofReal_injective (h4.trans h3)

private theorem span_top (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ) :
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
      v.embedding (x i)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun y _ => ?_
  set T := Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
    v.embedding (x i)) with hT
  have hs : ∀ (i : Fin n) (g : InfinitePlace F → ℂ),
      (fun v => Pi.single i (g v) : InfinitePlace F → Fin n → ℂ) ∈ T := by
    intro i g
    let S : (InfinitePlace F → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
      { toFun := fun g v => Pi.single i (g v)
        map_add' := fun a b => by funext v; simp [Pi.single_add]
        map_smul' := fun r a => by
          funext v j
          by_cases h : j = i
          · subst h
            simp
          · simp [h] }
    have hle : Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) ≤
        T.comap S := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨Pi.single i a, ?_⟩
      funext v j
      by_cases h : j = i
      · subst h
        simp [S]
      · simp [S, h]
    exact hle (by rw [GlobalTheory.LKTrip.HTGroup.span_real_embedding_places]; trivial)
  have hy : y = ∑ i : Fin n, fun v => (Pi.single i (y v i) : Fin n → ℂ) := by
    funext v j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => hs i fun v => y v i

theorem archSpan_of : ArchSpan := by
  intro F _ _ _ n
  refine ⟨span_top F n, ?_, trace_eq_sum_places F⟩
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [← two_mul_card_places F]
  ring

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixGa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem isCoordA_of_dvd {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.fixGa_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.IntMult → UpperTheory.Gal.W2.FixGa := by
  intro hHC hLI hFL hAY hIM
  unfold FixGa
  intro p _ D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD D' t hcls P j a hco x e hU y hsee
  obtain ⟨hpl, hca, hloc, Q₀, hQ₀, hQ₀j, hrel⟩ := hco
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hP, he, hinc, hj, hpl'', hco'', hloc''⟩ :=
    hHC p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₂ hX hL hX' hL' ρ hfine D' t P x e hU B j a.1.1
      (PD.lat a.1.2) hpl hca hloc
  obtain ⟨hfix, hS, hK⟩ := hsee
  have hN : 0 < N := by omega
  have hS' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS
  obtain ⟨w, hw, hwj⟩ := (hLI p D G L B PD N hN hcp D' t D'' t'' j j'' a.1 (a.1.1 * h⁻¹, a.1.2) N' N t t''
    hcls hcls'' hpl hpl'' (isCoordA_of_dvd L hd hca) hco'' hloc hloc'' y⁻¹).1 (by
      constructor
      · have := (L.KN N).inv_mem hS'
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this
      · have := (KHT p G.m G.n 1 G.Fw).inv_mem hK
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this)
  have hfix' := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y).2 hfix
  obtain ⟨H, hH⟩ := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y⁻¹).1.1 hfix'
  have hga : ∀ u, j (w (inc u)) = actY L y⁻¹ (j u) := fun u => by rw [hwj, hj]
  have hQQ : ∀ Q : VQ D →+ Fin D.g → ℂ, (∀ u, Q (j u) = P u) → ∀ w₀, Q w₀ = Q₀ w₀ := by
    intro Q hQj w₀
    obtain ⟨m, u, hm, hmu⟩ := hpl.2.2.1 w₀
    apply smul_right_injective (Fin D.g → ℂ) hm
    simp only
    rw [← map_nsmul Q, ← map_nsmul Q₀, hmu, hQj, hQ₀j]
  obtain ⟨s, hs, hEF⟩ := hpl.2.2.2
  have hpos : (0 : ℚ) < ((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 := (y⁻¹).2.2
  have hmul : ∀ u u' : D'.La, (((D'.EF ((w.toLinearMap ∘ₗ inc) u)) ((w.toLinearMap ∘ₗ inc) u') : ℤ) : ℚ) =
      (((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 : ℚ) * ((D'.EF u u' : ℤ) : ℚ) := by
    intro u u'
    show (((D'.EF (w (inc u))) (w (inc u')) : ℤ) : ℚ) = _
    rw [hEF, hEF, hga, hga, (hAY p D G L B.β y⁻¹).1]
    ring
  obtain ⟨m, hm, hm'⟩ := hIM D.O D.inv D' (w.toLinearMap ∘ₗ inc) _ hpos hmul
  refine ⟨w.toLinearMap ∘ₗ inc, H, fun u => hga u, ⟨⟨m, hm, hm'⟩, fun u => ?_⟩, fun w' Q hQj hQ => ?_⟩
  · show P (w (inc u)) = H *ᵥ P u
    rw [← hQ₀j, ← hQ₀j, hga, hH]
  · rw [hQQ Q hQj, hQQ Q hQj, hH]
end

