module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixMatCond

theorem eq_θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Y : Scheme.{0}} (φ : Y ⟶ A.left)
    (ψ : Y ⟶ (topS Rg ⊗ A).left) (h : ψ ≫ (snd (topS Rg) A).left = φ) : ψ = φ ≫ θ A := by
  let Y0 : Over (Sp Rg) := Over.mk (φ ≫ A.hom)
  have w1 : ψ ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [← h, Category.assoc, Over.w (snd (topS Rg) A)]
  have w2 : (φ ≫ θ A) ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [Category.assoc, ← Over.w (snd (topS Rg) A), ← Category.assoc (θ A), θ_snd, Category.id_comp]
  let u : Y0 ⟶ topS Rg ⊗ A := Over.homMk ψ w1
  let v : Y0 ⟶ topS Rg ⊗ A := Over.homMk (φ ≫ θ A) w2
  have : u = v := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      haveI : Mono (topS Rg).hom := by dsimp [topS, overRes]; infer_instance
      rw [← cancel_mono (topS Rg).hom]
      simp only [Over.comp_left, Category.assoc, Over.w]
      try exact w1.trans w2.symm
    · ext
      simp only [Over.comp_left, u, v, Over.homMk_left, Category.assoc, θ_snd, Category.comp_id, h]
  exact congrArg CommaMorphism.left this

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ}
    (a : Fin n → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (t z) ∈ U)
    (f : Γ(X, U)) : gs (t ≫ g) z U f = (t.stalkMap z).hom (gs g (t z) U f) := by
  rw [← gs_pull t g z U h, gs_stalkMap t z _ h, gs_pull (𝟙 _) g (t z) U h, Category.id_comp]

theorem gs_appTop' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (a : Γ(X, ⊤)) :
    gs (𝟙 Y) y ⊤ (f.appTop.hom a) = gs f y ⊤ a :=
  (gs_pull (𝟙 _) f y ⊤ trivial a).trans (by rw [Category.id_comp])

theorem mem_wchart_one {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (j : Fin 1 → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : Fin 1 => m) j ↔ m y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem mem_wchart_unit {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (q : L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : PUnit => m) (fun _ => q) ↔ m y ∈ L.U q :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem app_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) :
    g (f x) = h x := by
  rw [← e]; rfl

theorem mem_wchart_comp {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (g : Y ⟶ X) (j : Fin 1 → L.ι) (z : Z)
    (h : f z ∈ LB.wchart L (fun _ : Fin 1 => g) j) : (𝟙 Z) z ∈ LB.wchart L (fun _ : Fin 1 => f ≫ g) j :=
  (mem_wchart_one L (f ≫ g) j ((𝟙 Z) z)).2 ((mem_wchart_one L g j (f z)).1 h)

end GlobalTheory.HomFixMatCond

namespace GlobalTheory.HomFixMatCond

theorem mat_cond : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM hcov hvA hvB hT hMat
  obtain ⟨hpA, hpB, hΦ, -⟩ := hT
  obtain ⟨ψA, ψB, α, hA, hB, -, hnorm, hmat⟩ := hMat
  obtain rfl := eq_θ A φA' ψA hA
  obtain rfl := eq_θ B φB' ψB hB
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A'.left) (z : Z) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι))
      (_ : r z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (j : Fin mB),
      gs (r ≫ Φ'.left ≫ φB' ≫ θ B) z ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs r z _ (α.s p).val * ∑ i, gs (r ≫ A'.hom) z ⊤ (c i j) *
          gs (r ≫ φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) := by
    intro Z r z p hz j
    have e := congrArg (gs r z _) (hmat j p)
    erw [gs_appLE _ _ _ _ r z hz, gs_mul r z _ hz, gs_sum' r z _ hz] at e
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul r z _ hz]
      erw [gs_appLE _ _ _ _ r z hz, gs_appLE _ _ _ _ r z hz]
      all_goals rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z q hq
    have hz : (Φ'.left ≫ φB' ≫ θ B) z ∈ ⨆ j, nonzeroLocus (bB j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    unfold nonzeroLocus at hj
    obtain ⟨kk, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hkU := (topS Rg ⊗ B).left.basicOpen_le _ hk
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hkU, mem_wchart_comp _ _ _ _ _ hq⟩
    have e := key (𝟙 _) z (kk, q) hzU j
    simp only [Category.id_comp] at e
    refine ⟨j, ?_⟩
    have hu : IsUnit (gs (Φ'.left ≫ φB' ≫ θ B) z _ ((bB j).f kk)) := by
      rw [gs_eq _ _ _ hkU]
      have : z ∈ A'.left.basicOpen (((Φ'.left ≫ φB' ≫ θ B).app _).hom ((bB j).f kk)) := by
        rw [← Scheme.preimage_basicOpen]; exact hk
      exact (Scheme.mem_basicOpen _ _ _ _).1 this
    rw [e] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro z q kk hq hk j j'
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hk, mem_wchart_comp _ _ _ _ _ hq⟩
    have e1 := key (𝟙 _) z (kk, q) hzU j
    have e2 := key (𝟙 _) z (kk, q) hzU j'
    simp only [Category.id_comp] at e1 e2
    have hc : ∀ j, comb bA (φA' ≫ θ A) A'.hom c z q j = ∑ i, gs A'.hom z ⊤ (c i j) *
        gs (φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U q) ((bA i).f q) := fun _ => rfl
    rw [hc, hc, e1, e2]
    ring
  · intro j
    apply fn_ext
    intro x _
    obtain ⟨qA, hqA⟩ := exists_chart hL (eSec A (t x))
    obtain ⟨qB, hqB⟩ := exists_chart hM (eSec B (t x))
    have F2 : zeroPt A' ≫ φA' = t ≫ eSec A := GlobalTheory.PolBaseChange.eSec_comm hpA
    have F3 : zeroPt A' ≫ Φ'.left ≫ φB' = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
        show η[A'].left ≫ Φ'.left = η[B'].left
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, h0]; exact GlobalTheory.PolBaseChange.eSec_comm hpB
    have F1 : zeroPt A' ≫ A'.hom = 𝟙 _ := Over.w η[A']
    have GA : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by rw [reassoc_of% F2]
    have GB : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by rw [reassoc_of% F3]
    let p : (Fin 1 → M.ι) × (Fin 1 → L.ι) := (fun _ => qB, fun _ => qA)
    have hx0 : zeroPt A' x ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := by
      refine ⟨(mem_wchart_one _ _ _ _).2 ?_, (mem_wchart_one _ _ _ _).2 ?_⟩
      · rw [app_of_comp (f := zeroPt A') (g := (Φ'.left ≫ φB' ≫ θ B) ≫ (snd (topS Rg) B).left)
          (h := t ≫ eSec B) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F3)]
        exact hqB
      · rw [app_of_comp (f := zeroPt A') (g := (φA' ≫ θ A) ≫ (snd (topS Rg) A).left)
          (h := t ≫ eSec A) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F2)]
        exact hqA
    have hmemA : (eSec A ≫ θ A) (t x) ∈ (LPow A L (k : ℤ) (topS Rg)).U p.2 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec A ≫ θ A) (g := (snd (topS Rg) A).left) (h := eSec A)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqA
    have hmemB : (eSec B ≫ θ B) (t x) ∈ (LPow B M (k : ℤ) (topS Rg)).U p.1 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec B ≫ θ B) (g := (snd (topS Rg) B).left) (h := eSec B)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqB
    have hWA : t x ∈ (L.pull (eSec A)).U (fun _ => p.2 0) := (mem_wchart_unit _ _ _ _).2 hqA
    have hWB : t x ∈ (M.pull (eSec B)).U (fun _ => p.1 0) := (mem_wchart_unit _ _ _ _).2 hqB
    have hIA : ∀ i, gs (t ≫ eSec A ≫ θ A) x ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) =
        gs t x ⊤ (αA i) * gs t x _ (eA.s (fun _ => qA)).val ^ k := by
      intro i
      rw [gs_comp_stalk _ _ _ _ hmemA, hvA i (t x) p.2 hmemA, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eA.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWA, ← gs_stalkMap t x _ hWA]
    have hIB : gs (t ≫ eSec B ≫ θ B) x ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs t x ⊤ (βB j) * gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      rw [gs_comp_stalk _ _ _ _ hmemB, hvB j (t x) p.1 hmemB, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eB.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWB, ← gs_stalkMap t x _ hWB]
    have hxW : (𝟙 (Sp R)) x ∈ (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p ⊓
        t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
        t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := ⟨⟨hx0, hWA⟩, hWB⟩
    have hN : gs (zeroPt A') x _ (α.s p).val * gs t x _ (eA.s (fun _ => qA)).val ^ k =
        gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      have e := congrArg (gs (𝟙 (Sp R)) x _) (hnorm p)
      rw [gs_mul _ _ _ hxW, gs_pow' _ _ _ hxW, gs_pow' _ _ _ hxW] at e
      erw [gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW] at e
      simp only [Category.id_comp] at e
      exact e
    have eK := key (zeroPt A') x p hx0 j
    rw [GA, GB, F1, hIB] at eK
    simp only [hIA] at eK
    have heb : IsUnit (gs t x _ (eB.s (fun _ => qB)).val) := by
      rw [gs_unit t x _ hWB]; exact Units.isUnit _
    rw [gs_appTop', gs_sum' (𝟙 (Sp R)) x ⊤ trivial]
    simp only [gs_mul (𝟙 (Sp R)) x ⊤ trivial, gs_appTop']
    apply (heb.pow k).mul_left_inj.1
    rw [eK, ← hN, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.HomFixMatCond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLie
section
noncomputable section

namespace GlobalTheory.UnitLemma.OrbitAll

open GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem isIso_stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem isIso_kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem isIso_identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [isIso_kapSum_eq h₁ h₂, isIso_stSum_eq h₁, isIso_stSum_eq h₂, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

theorem prod_aeval (B₁ B₂ : InvAlg K) (f : K.O[X]) :
    aeval (B₁.prod B₂).g f = ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) :=
  Prod.ext (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm

theorem prod_integral (B₁ B₂ : InvAlg K) (h₁ : IsIntegral K.O B₁.g) (h₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g :=
  IsIntegral.pair (x := (B₁.g, B₂.g)) h₁ h₂

theorem eq_one_of_finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e)
    (h : Module.finrank K.E (cut B e he).A = 0) : e = 1 := by
  have : Subsingleton (B.A ⧸ Ideal.span {e}) := (Module.finrank_zero_iff (R := K.E) (M := (cut B e he).A)).1 h
  have h1 : (1 : B.A) ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  linear_combination (e - 1) * -ha + a * hi.eq

theorem finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    Module.finrank K.E B.A = Module.finrank K.E (cut B e he).A +
      Module.finrank K.E (cut B (1 - e) (one_sub_fixed B he)).A := by
  rw [(AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp)
    (by simp [hi])).toLinearEquiv.finrank_eq, Module.finrank_prod]
  rfl

theorem charpoly_eq_mul_charpoly_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    B.P = (cut B e he).P * (cut B (1 - e) (one_sub_fixed B he)).P := by
  rw [← prod_P, (isIso_cut B hi he).charpoly_eq_of_isIso]

theorem one_orbit (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (h : ∀ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → B.σ e = e → e = 0 ∨ e = 1) :
    (∃ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e ∧ e + B.σ e = 1) ∨
      IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A)) := by
  rcases subsingleton_or_nontrivial B.A with hs | hs
  · exact Or.inl ⟨0, zero_mem _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hid : ∀ e : Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → e = 0 ∨ e = 1
  · have : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
      Module.Finite.iff_fg.2 hi.fg_adjoin_singleton
    exact Or.inr (isLocalRing_of_idem (R := K.O) _ hid)
  push Not at hid
  obtain ⟨⟨e, he⟩, hee, h0, h1⟩ := hid
  have hee : e * e = e := congrArg Subtype.val hee
  have h0 : e ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : e ≠ 1 := fun h => h1 (Subtype.ext h)
  have he' := adjoin_stable B hu hi he
  have hee' : B.σ e * B.σ e = B.σ e := by rw [← map_mul, hee]
  have hm : e * B.σ e = 0 := by
    refine (h _ (mul_mem he he') ?_ ?_).resolve_right fun h2 => h1 ?_
    · linear_combination B.σ e * B.σ e * hee + e * hee'
    · rw [map_mul, B.σ_σ, mul_comm]
    · linear_combination (1 - e) * h2 + B.σ e * hee
  refine Or.inl ⟨e, he, hee, (h _ (add_mem he he') ?_ ?_).resolve_left fun h2 => h0 ?_⟩
  · linear_combination hee + hee' + 2 * hm
  · rw [map_add (f := _), B.σ_σ, add_comm]
  · linear_combination e * h2 - hee - hm

theorem identity_integral (hL : UnitLemmaLie) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact _root_.GlobalTheory.UnitLemma.Swap.identity_of_swap K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact _root_.GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any hL K B₁ B₂ u₁ u₂ hs i₁ i₂ h
  push Not at h
  obtain ⟨e, he, hee, hσ, h0, h1⟩ := h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨f, hf⟩ := he
  have hf : ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) = e := (prod_aeval B₁ B₂ f).symm.trans hf
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨f₁, f₂⟩ := Prod.ext_iff.1 hf
  have j₁ : IsIdempotentElem e₁ := congrArg Prod.fst hee
  have j₂ : IsIdempotentElem e₂ := congrArg Prod.snd hee
  have s₁ : B₁.σ e₁ = e₁ := congrArg Prod.fst hσ
  have s₂ : B₂.σ e₂ = e₂ := congrArg Prod.snd hσ
  dsimp only at f₁ f₂
  have r₁ := finrank_cut B₁ j₁ s₁
  have r₂ := finrank_cut B₂ j₂ s₂
  have p₁ : Module.finrank K.E (cut B₁ e₁ s₁).A + Module.finrank K.E (cut B₂ e₂ s₂).A ≠ 0 := fun hz =>
    h1 (Prod.ext (eq_one_of_finrank_cut B₁ j₁ s₁ (Nat.add_eq_zero_iff.1 hz).1)
      (eq_one_of_finrank_cut B₂ j₂ s₂ (Nat.add_eq_zero_iff.1 hz).2))
  have p₂ : Module.finrank K.E (cut B₁ (1 - e₁) (one_sub_fixed B₁ s₁)).A +
      Module.finrank K.E (cut B₂ (1 - e₂) (one_sub_fixed B₂ s₂)).A ≠ 0 := fun hz =>
    h0 (Prod.ext
      (sub_eq_self.1 (eq_one_of_finrank_cut B₁ j₁.one_sub (one_sub_fixed B₁ s₁) (Nat.add_eq_zero_iff.1 hz).1))
      (sub_eq_self.1 (eq_one_of_finrank_cut B₂ j₂.one_sub (one_sub_fixed B₂ s₂) (Nat.add_eq_zero_iff.1 hz).2)))
  rw [charpoly_eq_mul_charpoly_cut B₁ j₁ s₁, charpoly_eq_mul_charpoly_cut B₂ j₂ s₂, mul_mul_mul_comm] at hs
  refine isIso_identity (isIso_cut B₁ j₁ s₁) (isIso_cut B₂ j₂ s₂) ?_
  refine _root_.GlobalTheory.UnitLemma.ProdId.identity_prod K _ _ _ _ hs (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂) (cut_integral _ _ _ i₁)
    (cut_integral _ _ _ i₂) ?_ ?_ ?_
  · rw [← prod_P, ← prod_P] at hs ⊢
    refine val_resultant _ _ hs.of_mul_left hs.of_mul_right
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂))
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)) f ?_ ?_
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₁))).symm
        (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₂))).symm
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_left
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_right
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)

theorem identity_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.OrbitAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_diagonal_pullback_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift u u) (lift v v) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n u v c' → c = c' := by
  first | (exact @GlobalTheory.DiagPull.weilIs_diag_eq) | (exact GlobalTheory.DiagPull.weilIs_diag_eq) | (intros; apply GlobalTheory.DiagPull.weilIs_diag_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitoneStatement
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, ¬ Antitone l → W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i)) = 0 := by
  first | exact @GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone | exact GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone | (intros; apply GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone <;> assumption)
end

