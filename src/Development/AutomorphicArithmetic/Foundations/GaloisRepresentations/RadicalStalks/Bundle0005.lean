module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OneLeft
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem sp {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem one_left' {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    (1 : T ⟶ A).left = T.hom ≫ η[A].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

private theorem eta_comp {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ : A.left ⟶ A.left}
    (hψ : SMor A σ ψ) : η[A].left ≫ ψ = spMap σ ≫ η[A].left := by
  let T : Over (Sp k) := 𝟙_ (Over (Sp k))
  let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk (η[A].left ≫ ψ) (by
    have h1 := Over.w η[A]
    have h2 := hψ.w
    simp only [Category.assoc, h2]
    rw [← Category.assoc, h1]
    rfl)
  have h := hψ.mul T (1 : T ⟶ A) (1 : T ⟶ A) x₀ x₀ (by simp [x₀, one_left'] ; rfl) (by simp [x₀, one_left']; rfl)
  have h1 : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h, _root_.mul_one]
    simp [x₀, one_left']
    rfl
  have h2 : x₀ = 1 := by simpa using h1
  have h3 := congrArg Over.Hom.left h2
  rw [one_left'] at h3
  have h4 : T.hom = 𝟙 _ := rfl
  simpa [x₀, h4] using h3

private theorem tan_left {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {w : epsR k ⟶ A} (hw : IsTangent w) :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = η[A].left := by
  have h0 := congrArg Over.Hom.left ((GlobalTheory.GrpTangent.isTangent_iff w).1 hw)
  rw [Over.comp_left, one_left'] at h0
  have h1 : (GlobalTheory.GrpTangent.epsZero k).left ≫ w.left = η[A].left := by simpa using h0
  exact h1

theorem UpperTheory.Gal.Ord.tan :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
      ∀ (σ : k →+* k) (ψ : A.left ⟶ A.left) (hψ : SMor A σ ψ), Function.Surjective σ →
      ∀ v : epsR k ⟶ A, IsTangent v →
        ((∀ f : Form (A.hom ≫ 𝟙 _), Form.cl _ f ∈ primDR A → tanVal v (hψ.isMor.pullForm f) = 0) ↔
          IsConst (v.left ≫ ψ)) := by
  intro k _ A _ hA σ ψ hψ hs v hv
  let e : k ≃+* k := RingEquiv.ofBijective σ ⟨σ.injective, hs⟩
  let τ : k →+* k := (e.symm : k →+* k)
  have τσ : τ.comp σ = RingHom.id k := RingHom.ext fun x ↦ e.symm_apply_apply x
  have στ : σ.comp τ = RingHom.id k := RingHom.ext fun x ↦ e.apply_symm_apply x
  let d := Chart.dualMapR τ
  let u := Chart.dualMapR σ
  let fst : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  let alg := algebraMap k (DualNumber k)
  have ud : u.comp d = RingHom.id _ := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [d, u, Chart.dualMapR, ← RingHom.comp_apply, στ]
  have fd : fst.comp d = τ.comp fst := by
    refine RingHom.ext fun x ↦ ?_
    simp [d, fst, Chart.dualMapR]
  have dalg : d.comp (alg.comp σ) = alg := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [d, alg, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl, ← RingHom.comp_apply, τσ]
  have dc : d.comp (alg.comp fst) = (alg.comp fst).comp d := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [d, alg, fst, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have cu : (alg.comp fst).comp (u.comp alg) = u.comp alg := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [u, alg, fst, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : epsR k ⟶ A := Over.homMk (spMap d ≫ v.left ≫ ψ) (by
    have hv0 := Over.w v
    have h2 := hψ.w
    change (spMap d ≫ v.left ≫ ψ) ≫ A.hom = spMap alg
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc v.left, hv0]
    change spMap d ≫ spMap alg ≫ spMap σ = _
    rw [sp, sp, dalg])
  have e1 : v.left ≫ ψ = spMap u ≫ v'.left := by
    change _ = spMap u ≫ spMap d ≫ v.left ≫ ψ
    rw [← Category.assoc, sp, ud, spMap_id, Category.id_comp]
  have hval := fun f ↦ GlobalTheory.LieDual.tanVal_pullForm_baseChange (v := v') (v' := v) hψ.isMor e1 f
  have htan : IsTangent v' := by
    rw [GlobalTheory.GrpTangent.isTangent_iff]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left']
    change spMap fst ≫ spMap d ≫ v.left ≫ ψ = 𝟙 _ ≫ η[A].left
    have h00 : spMap fst ≫ v.left = η[A].left := tan_left hv
    calc spMap fst ≫ spMap d ≫ v.left ≫ ψ = (spMap fst ≫ spMap d) ≫ v.left ≫ ψ := by rw [Category.assoc]
      _ = (spMap τ ≫ spMap fst) ≫ v.left ≫ ψ := by rw [sp, sp, fd]
      _ = spMap τ ≫ (spMap fst ≫ v.left) ≫ ψ := by simp only [Category.assoc]
      _ = spMap τ ≫ η[A].left ≫ ψ := by rw [h00]
      _ = (spMap τ ≫ spMap σ) ≫ η[A].left := by rw [eta_comp hψ, Category.assoc]
      _ = 𝟙 _ ≫ η[A].left := by rw [sp, τσ, spMap_id]; rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA
  have L : LieExact A := (GlobalTheory.abelianDeRham.2.1 k A g hA hg).1
  constructor
  · intro h
    have h0 : ∀ f : Form (A.hom ≫ 𝟙 _), Form.cl _ f ∈ primDR A → tanVal v' f = 0 := fun f hf ↦
      (map_eq_zero σ).1 ((hval f).symm.trans (h f hf))
    obtain ⟨H, hH⟩ := L.2 v' htan
    have hF : H ∈ Fil A := mem_Fil.2 fun f hf ↦ by rw [hH.2, h0 f hf]
    have h1 : v' = 1 := (L.1 H).unique hH (isLieImage_one_iff.2 hF)
    have h2 : v'.left = spMap alg ≫ η[A].left := by rw [h1, one_left']; rfl
    have h3 : spMap (alg.comp fst) ≫ spMap u ≫ spMap alg = spMap u ≫ spMap alg := by
      rw [sp, sp, cu]
    change spMap (alg.comp fst) ≫ v.left ≫ ψ = v.left ≫ ψ
    rw [e1, h2]
    simpa only [Category.assoc] using h3 =≫ η[A].left
  · intro h f hf
    have h' : spMap (alg.comp fst) ≫ v.left ≫ ψ = v.left ≫ ψ := h
    have h1 : v'.left = spMap (alg.comp fst) ≫ v'.left := by
      change spMap d ≫ v.left ≫ ψ = spMap (alg.comp fst) ≫ spMap d ≫ v.left ≫ ψ
      calc spMap d ≫ v.left ≫ ψ = spMap d ≫ spMap (alg.comp fst) ≫ v.left ≫ ψ := by rw [h']
        _ = (spMap d ≫ spMap (alg.comp fst)) ≫ v.left ≫ ψ := by rw [Category.assoc]
        _ = (spMap (alg.comp fst) ≫ spMap d) ≫ v.left ≫ ψ := by rw [sp, sp, dc]
        _ = _ := by rw [Category.assoc]
    have h2 : v' = 1 := by
      apply Over.OverMorphism.ext
      rw [one_left', h1, ← sp, Category.assoc, tan_left htan]
      rfl
    rw [hval, h2, tanVal_one, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PullFrobIter
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section SlopeTestRemainingChoices

open GlobalTheory.Published.AbelianDeRham

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
  {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}

private theorem pull_primPull (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (e : A ⟶ A) (e' : A' ⟶ A')
    [IsMonHom e] [IsMonHom e'] (he : e'.left ≫ φ = φ ≫ e.left) (c : primDR A) :
    (bcMor h).pull (primPull (dp0 R) (𝟙 _) e c) = primPull (dp0 R') (𝟙 _) e' ((bcMor h).pull c) := by
  have e1 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) e) (bcMor h)
    (GlobalTheory.DeRham.GrpMor.comp (homMor (dp0 R) (𝟙 _) e) (bcMor h)) (fun _ => rfl) rfl c
  have e2 := GrpMor.pull_pull (bcMor h) (homMor (dp0 R') (𝟙 _) e')
    (GlobalTheory.DeRham.GrpMor.comp (homMor (dp0 R) (𝟙 _) e) (bcMor h)) (fun _ => rfl) he c
  exact e1.trans e2.symm

private theorem pull_frob_iter (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (f : ℕ) (c : primDR A) :
    (bcMor h).pull ((frobDR p R hR A)^[f] c) = (frobDR p R' hR' A')^[f] ((bcMor h).pull c) := by
  induction f with
  | zero => rfl
  | succ f ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', GlobalTheory.LinFrob.pull_frobDR p hR hR' h, ih]

private theorem frob_iter_smul (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (f : ℕ) (r : R) (c : primDR A) :
    (frobDR p R hR A)^[f] (r • c) = r ^ p ^ f • (frobDR p R hR A)^[f] c := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GlobalTheory.LinFrob.frobDR_smul p hR, pow_succ,
      pow_mul]

private theorem pull_mem_span (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (g : A ⟶ A) (g' : A' ⟶ A') [IsMonHom g] [IsMonHom g']
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) {y : primDR A}
    (hy : y ∈ Submodule.span R (Set.range fun c => primPull (dp0 R) (𝟙 _) g ((frobDR p R hR A)^[f] c))) :
    (bcMor h).pull y ∈
      Submodule.span R' (Set.range fun c => primPull (dp0 R') (𝟙 _) g' ((frobDR p R' hR' A')^[f] c)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    refine Submodule.subset_span ⟨(bcMor h).pull c, ?_⟩
    simp only
    rw [pull_primPull h g g' hg, pull_frob_iter p hR hR' h]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ ha

private theorem no_up (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (d : ℕ) (hA : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension d A.hom) (e g : A ⟶ A) (e' g' : A' ⟶ A')
    [IsMonHom e] [IsMonHom g] [IsMonHom e'] [IsMonHom g'] (he : e'.left ≫ φ = φ ≫ e.left)
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) (hN : NO p R hR A e g f) : NO p R' hR' A' e' g' f := by
  unfold NO at hN ⊢
  intro x hx
  rw [(GlobalTheory.abelianDeRham.2.2.1 R A d hA hd R' A' φ h).2] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    rw [← pull_primPull h e e' he]
    exact pull_mem_span p hR hR' h g g' hg f (hN c hc)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

end SlopeTestRemainingChoices

section Down

open GlobalTheory.Published.AbelianDeRham

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Over (Sp K)} [GrpObj A]
  {A' : Over (Sp L)} [GrpObj A'] {φ : A'.left ⟶ A.left}

private theorem mem_of_subtype_baseChange_eq_one_tmul {K L : Type} {V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (y : V) (s : L ⊗[K] W) (hs : (W.subtype.baseChange L) s = (1 : L) ⊗ₜ[K] y) : y ∈ W := by
  have hcomp : W.mkQ ∘ₗ W.subtype = 0 := by
    ext w
    exact (Submodule.Quotient.mk_eq_zero W).mpr w.2
  have hq : (W.mkQ.baseChange L) ((W.subtype.baseChange L) s) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [hs, LinearMap.baseChange_tmul] at hq
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (TensorProduct.lid K (V ⧸ W)) (LinearMap.rTensor (V ⧸ W) g ((1 : L) ⊗ₜ[K] W.mkQ y)) = 0 := by
    rw [hq, map_zero, map_zero]
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hg1, one_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h2
  exact h2


set_option maxHeartbeats 200000 in
private theorem no_down (p : ℕ) [Fact p.Prime] (hK : (p : K) = 0) (hL : (p : L) = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap K L)) φ) (d : ℕ) (hA : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension d A.hom) (e g : A ⟶ A) (e' g' : A' ⟶ A')
    [IsMonHom e] [IsMonHom g] [IsMonHom e'] [IsMonHom g'] (he : e'.left ≫ φ = φ ≫ e.left)
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) (hN : NO p L hL A' e' g' f) : NO p K hK A e g f := by
  obtain ⟨-, -, hBC, -, -⟩ := GlobalTheory.abelianDeRham
  obtain ⟨hbij, hF⟩ := hBC K A d hA hd L A' φ h
  unfold NO at hN ⊢
  intro x hx
  have hPx : (bcMor h).pull x ∈ PrimitiveSubmodule A' := by
    rw [hF]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hy' := hN _ hPx
  rw [← pull_primPull h e e' he] at hy'
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span K
      (Set.range fun c => primPull (dp0 K) (𝟙 (Sp K)) g ((frobDR p K hK A)^[f] c)) := ⟨_, rfl⟩
  rw [← hW]
  let Φ : L ⊗[K] W →ₗ[L] primDR A' := (liftSemi (bcMor h).pull).comp (W.subtype.baseChange L)
  have hΦ : ∀ (a : L) (w : W), Φ (a ⊗ₜ[K] w) = a • (bcMor h).pull (w : primDR A) := by
    intro a w
    simp only [Φ, LinearMap.comp_apply, LinearMap.baseChange_tmul, liftSemi_tmul, Submodule.subtype_apply]
  have hgen : ∀ t : L ⊗[K] primDR A,
      primPull (dp0 L) (𝟙 (Sp L)) g' ((frobDR p L hL A')^[f] (liftSemi (bcMor h).pull t)) ∈ LinearMap.range Φ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, iterate_map_zero, map_zero]
      exact Submodule.zero_mem _
    | tmul a v =>
      rw [liftSemi_tmul, frob_iter_smul p hL f a, ← pull_frob_iter p hK hL h f v, map_smul,
        ← pull_primPull h g g' hg]
      have hmem : primPull (dp0 K) (𝟙 (Sp K)) g ((frobDR p K hK A)^[f] v) ∈ W := by
        rw [hW]
        exact Submodule.subset_span ⟨v, rfl⟩
      exact LinearMap.mem_range.mpr ⟨(a ^ p ^ f) ⊗ₜ[K] (⟨_, hmem⟩ : W), hΦ _ _⟩
    | add t1 t2 h1 h2 =>
      rw [map_add (f := _), iterate_map_add, map_add (f := _)]
      exact Submodule.add_mem _ h1 h2
  have hle : Submodule.span L (Set.range fun c => primPull (dp0 L) (𝟙 (Sp L)) g' ((frobDR p L hL A')^[f] c)) ≤
      LinearMap.range Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨t, ht⟩ := hbij.2 c
    have h4 := hgen t
    rw [SetLike.mem_coe, ← ht]
    exact h4
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp (hle hy')
  simp only [Φ, LinearMap.comp_apply] at hs
  have h5 : liftSemi (bcMor h).pull (W.subtype.baseChange L s) =
      liftSemi (bcMor h).pull ((1 : L) ⊗ₜ[K] primPull (dp0 K) (𝟙 (Sp K)) e x) := by
    rw [liftSemi_tmul, one_smul]
    exact hs
  have h6 := hbij.1 h5
  exact mem_of_subtype_baseChange_eq_one_tmul W _ s h6

end Down

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.desc :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (f : ℕ) (π : Par p w f)
      (κ k T : Type) [Field κ] [Field k] [CommRing T] (hκ : (p : κ) = 0) (hk : (p : k) = 0) (hT : (p : T) = 0) (σ : κ →+* k) (τ : κ →+* T)
      (s : Sp κ ⟶ Sp R) (s₀ : Sp k ⟶ Sp R) (s' : Sp T ⟶ Sp R) (o : Obj b N s) (o₀ : Obj b N s₀) (o' : Obj b N s'),
      ObjMap o₀ o (spMap σ) → ObjMap o' o (spMap τ) → NOo hk o₀ π → NOo hT o' π := by
  intro p _ D R _ b N w f π κ k T _ _ _ hκ hk hT σ τ s s₀ s' o o₀ o' m₀ m' hN
  letI : Algebra κ k := σ.toAlgebra
  letI : Algebra κ T := τ.toAlgebra
  haveI := o.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  haveI := o₀.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o₀.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  haveI := o'.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o'.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  have hd := _root_.GlobalTheory.HTDim.relDim_and_isLB p D R b N _ s o
  have h1 : NOo hκ o π :=
    no_down p hκ hk m₀.cart D.g o.ab hd.1 (o.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
      (o.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (o₀.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
      (o₀.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (m₀.act _) (m₀.act _) f hN
  exact no_up p hκ hT m'.cart D.g o.ab hd.1 (o.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
    (o.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (o'.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
    (o'.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (m'.act _) (m'.act _) f h1
end

