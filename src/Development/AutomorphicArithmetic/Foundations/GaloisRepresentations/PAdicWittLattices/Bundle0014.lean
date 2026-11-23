module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowHodge
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

private theorem isTr_transport {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} {p : Z ⟶ B}
    {q q' : Y ⟶ B} (e : q = q') {s : Y ⟶ Z} {tr : T.H q →ₗ[R] T.H p} (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} {r : X ⟶ B} (t : Y ⟶ X) (h₁ : t ≫ r = q) (h₂ : t ≫ r = q') (y : T.H r),
        tr' (T.pull t h₂ y) = tr (T.pull t h₁ y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ => rfl⟩

private theorem low_square {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : GlobalTheory.GalV.HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) :
    IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g) (pullback.fst C.p (gen O k)) := by
  have hls : (low D).s g ≫ pullback.snd C.p (gen O k) = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    bcMap_snd (gen O k) (D.s g) rfl
  have hlf : (low D).s g ≫ pullback.fst C.p (gen O k) = pullback.fst (D.s g ≫ C.p) (gen O k) ≫ D.s g :=
    bcMap_fst (gen O k) (D.s g) rfl
  refine IsPullback.of_bot ?_ hlf.symm (IsPullback.of_hasPullback C.p (gen O k))
  convert IsPullback.of_hasPullback (D.s g ≫ C.p) (gen O k) using 2
  exact hls

theorem UpperTheory.Gal.G3.jLowHodge :
    HodgeGood → BcGood.{0} → FEtBasic → HodgeOpBc → CoverInv.{0} → LiesOp.{0} → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge := by
  intro hHG hBG hFB hOB hCI hLO k L F _ _ _ _ φ ψ H θ O _ _ C D hN hO a hH
  unfold HOcc at hH ⊢
  unfold Nice at hN
  obtain ⟨b, x, hx, he⟩ := hH
  unfold IsHEig at he
  set T' := (hodge F a b).bc (Spec.map (CommRingCat.ofHom φ)) with hT'
  have hgood : T'.Good := hBG _ _ (hHG F a b)
  obtain ⟨hinj, hsurj⟩ := hCI C hO T' hgood
  have hH' : ∀ g : H.Γ, ∃ trg : T'.H (H.s g ≫ H.q) →ₗ[F] T'.H H.q,
      T'.IsTr H.q (H.s g ≫ H.q) (H.s g) trg ∧ trg (T'.pull (H.t g) (H.comm g) x) = ψ (θ g) • x := by
    intro g
    obtain ⟨d, hd⟩ := hN.2.2 g
    haveI : IsFinite (H.s g) := hd.1
    haveI : Etale (H.s g) := hd.2.1
    obtain ⟨i1, i2, tr, htr, heq⟩ := hOB k F φ H g a b
    obtain ⟨j1, j2, hg⟩ := he g
    exact ⟨tr, htr, (heq j1 j2 x).symm.trans hg⟩
  obtain ⟨z, hz⟩ := hsurj x (fun g _ hθ => by
    obtain ⟨trg, htr, heq⟩ := hH' g
    exact ⟨trg, htr, by rw [heq, hθ, map_one, one_smul]⟩)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hz]; exact map_zero _)
  refine ⟨b, z, hz0, ?_⟩
  unfold IsHEig
  intro g
  have hfet : FEt ((low D).s g) (D.d g) := hFB.1 _ _ _ _ _ (low_square D g) (D.fet g)
  haveI : IsFinite ((low D).s g) := hfet.1
  haveI : Etale ((low D).s g) := hfet.2.1
  obtain ⟨i1, i2, trL, htrL, heqL⟩ := hOB k F φ (low D) g a b
  refine ⟨i1, i2, ?_⟩
  rw [heqL i1 i2 z]
  obtain ⟨tr', htr', htrans⟩ := isTr_transport T' (q := (low D).s g ≫ (low D).q)
    (q' := pullback.snd (D.s g ≫ C.p) (gen O k)) (bcMap_snd (gen O k) (D.s g) rfl) htrL
  obtain ⟨trg, htrg, hgeq⟩ := hH' g
  have hlies := hLO C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet T' hgood tr' trg htr' htrg z
  rw [hz, hgeq, ← hz, ← map_smul] at hlies
  have h := hinj ((map_smul (T'.pull (piK C) _) (ψ (θ g)) z).trans hlies)
  have h₂ : bcMap (gen O k) (D.t g) (D.comm g) ≫ (low D).q = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    ((low D).comm g).trans (bcMap_snd (gen O k) (D.s g) rfl)
  have h3 : tr' (T'.pull (bcMap (gen O k) (D.t g) (D.comm g)) h₂ z) =
      trL (T'.pull ((low D).t g) ((low D).comm g) z) := htrans ((low D).t g) ((low D).comm g) h₂ z
  have h' : ψ (θ g) • z = ((D.m g : ℕ) : F) • trL (T'.pull ((low D).t g) ((low D).comm g) z) :=
    h.trans (congrArg (fun w => ((D.m g : ℕ) : F) • w) h3)
  have hm : ((D.m g : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
  have hw : trL (T'.pull ((low D).t g) ((low D).comm g) z) = ψ (θ g / (D.m g : L)) • z := by
    rw [map_div₀, map_natCast, div_eq_inv_mul, mul_smul, h']
    exact (inv_smul_smul₀ hm _).symm
  exact hw
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowPiece
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open Formalism.ConjugateSelfDual (Qbar)
universe u v

private theorem intertwine_of_restrict {K V₁ V₀ G : Type*} [Field K] [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₀] [Module K V₀] (f : V₁ →ₗ[K] V₀) (hf : Function.Injective f) {d₁ d₀ : ℕ}
    (W₁ : Submodule K V₁) (W₀ : Submodule K V₀) (b₁ : Module.Basis (Fin d₁) K W₁)
    (b₀ : Module.Basis (Fin d₀) K W₀) (hW : ∀ x ∈ W₁, f x ∈ W₀)
    (g₁ : G → V₁ →ₗ[K] V₁) (g₀ : G → V₀ →ₗ[K] V₀) (hc : ∀ σ x, g₀ σ (f x) = f (g₁ σ x))
    (ρ₁ : G → Matrix (Fin d₁) (Fin d₁) K) (ρ₀ : G → Matrix (Fin d₀) (Fin d₀) K)
    (h₁ : ∀ σ j, g₁ σ (b₁ j).1 = ∑ i, ρ₁ σ i j • (b₁ i).1)
    (h₀ : ∀ σ j, g₀ σ (b₀ j).1 = ∑ i, ρ₀ σ i j • (b₀ i).1) :
    ∃ A : Matrix (Fin d₀) (Fin d₁) K, Function.Injective A.mulVec ∧ ∀ σ, ρ₀ σ * A = A * ρ₁ σ := by
  let f' : W₁ →ₗ[K] W₀ := f.restrict hW
  have hf' : Function.Injective f' := fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h))
  let A := LinearMap.toMatrix b₁ b₀ f'
  have hA : ∀ j, f (b₁ j).1 = ∑ i, A i j • (b₀ i).1 := by
    intro j
    have e2 := congrArg W₀.subtype (b₀.sum_repr (f' (b₁ j)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simp only [A, LinearMap.toMatrix_apply]
    exact e2.symm
  refine ⟨A, ?_, fun σ => ?_⟩
  · intro v w h
    have key : ∀ u : Fin d₁ → K, A.mulVec u = b₀.repr (f' (b₁.equivFun.symm u)) := by
      intro u
      have hu : ⇑(b₁.repr (b₁.equivFun.symm u)) = u := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      have := LinearMap.toMatrix_mulVec_repr b₁ b₀ f' (b₁.equivFun.symm u)
      rw [hu] at this
      exact this
    rw [key, key] at h
    exact b₁.equivFun.symm.injective (hf' (b₀.repr.injective (Finsupp.ext fun i => congrFun h i)))
  · have hli : LinearIndependent K (fun i => (b₀ i).1) :=
      b₀.linearIndependent.map' W₀.subtype (Submodule.ker_subtype _)
    ext i j
    have e₁ : g₀ σ (f (b₁ j).1) = ∑ i, (ρ₀ σ * A) i j • (b₀ i).1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hA, map_sum]
      simp only [map_smul, h₀, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₂ : f (g₁ σ (b₁ j).1) = ∑ i, (A * ρ₁ σ) i j • (b₀ i).1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h₁, map_sum]
      simp only [map_smul, hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₃ : ∑ i, ((ρ₀ σ * A) i j - (A * ρ₁ σ) i j) • (b₀ i).1 = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← e₁, ← e₂, hc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.1 hli _ e₃ i)

private theorem galMap_bcMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ sp k} {q : Y ⟶ sp k} (f : Y ⟶ X) (h : f ≫ p = q) (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω q σ ≫ bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h =
      bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h ≫ galMap Ω p σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, galMap_fst, bcMap_fst, galMap_fst_assoc]
  · rw [Category.assoc, Category.assoc, bcMap_snd, galMap_snd, galMap_snd, reassoc_of% bcMap_snd]

theorem UpperTheory.Gal.G3.jLowPiece :
    HopLies → PieceLe → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := by
  intro hL hP E Ω _ _ _ _ _ l _ H θ O _ _ C D hN hO d₁ d₀ ρ₁ ρ₀ ⟨b₁, h₁⟩ ⟨b₀, h₀⟩
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  obtain ⟨hinj, -⟩ := hP l hl C hO Ω
  have hop' := fun g => hL l hl C D hN Ω g
  let P : Htot l (sch.obj ((low D).geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    (etG l E Ω).pull (piK C) (piK_snd C)
  have hop'' : ∀ g, hop l H Ω g ∘ₗ P = (D.m g : ℚ_[l]) • (P ∘ₗ hop l (low D) Ω g) := hop'
  have hinj' : Function.Injective (P.baseChange (Qbar l)) := hinj
  have hW : ∀ x ∈ piece l (low D) Ω (Qbar l) (fun g => θ g / D.m g),
      P.baseChange (Qbar l) x ∈ piece l H Ω (Qbar l) θ := by
    intro x hx
    simp only [piece, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro g
    have hm : ((D.m g : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
    have e : (hop l H Ω g).baseChange (Qbar l) (P.baseChange (Qbar l) x) =
        ((hop l H Ω g ∘ₗ P).baseChange (Qbar l)) x := by
      rw [LinearMap.baseChange_comp]; rfl
    rw [e, hop'', LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx g, map_smul, ← algebraMap_smul (Qbar l) (D.m g : ℚ_[l]), map_natCast,
      smul_smul, mul_div_cancel₀ _ hm]
  have hc : ∀ (σ : Ω ≃ₐ[E] Ω) x, galV l H Ω (Qbar l) σ (P.baseChange (Qbar l) x) =
      P.baseChange (Qbar l) (galV l (low D) Ω (Qbar l) σ x) := by
    intro σ x
    have e : galTot l Ω H.q σ ∘ₗ P = P ∘ₗ galTot l Ω (low D).q σ := by
      have e' := congrArg (fun u => pullTot l (sch.map u))
        (galMap_bcMap (Ω := Ω) (piK C) (piK_snd C) σ)
      simp only [Functor.map_comp, pullTot_comp] at e'
      exact e'
    have e2 := congrArg (fun u => LinearMap.baseChange (Qbar l) u x) e
    simp only [LinearMap.baseChange_comp] at e2
    exact e2
  exact intertwine_of_restrict _ hinj' _ _ b₁ b₀ hW (galV l (low D) Ω (Qbar l)) (galV l H Ω (Qbar l)) hc
    (fun σ => (ρ₁ σ).val) (fun σ => (ρ₀ σ).val) h₁ h₀
end

