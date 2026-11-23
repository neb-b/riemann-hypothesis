module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.LieSpanBaseChange

open GlobalTheory.CM.LieBaseChange IsDedekindDomain

theorem vec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {f : R →+* R'} {g : R' →+* R''}
    {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left}
    {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''} (h : IsVecOver f φ v v') (h' : IsVecOver g ψ v' v'') :
    IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  unfold IsVecOver at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc, ← PolFibre.dualMapR_comp]
  exact congrArg (· ≫ v.left) (spMap_comp_spMap _ _)

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {j : K →+* K'}

theorem algebraMap_comp_mapRingHom (j : K →+* K') :
    (algebraMap (𝓞 K') K').comp (RingOfIntegers.mapRingHom j) = j.comp (algebraMap (𝓞 K) K) := rfl

variable {P : Out.PolAV (Sp (𝓞 K))} {P' : Out.PolAV (Sp (𝓞 K'))} {ξ : P'.A.left ⟶ P.A.left} {F : GenFib P}
  {Q : Out.PolAV (Sp K')} {hd : SmoothOfRelativeDimension F.P₀.g Q.A.hom} {φ' : Q.A.left ⟶ P'.A.left}
  {fib : IsPolFibre (algebraMap (𝓞 K') K') P' (withDim Q F.P₀.g hd) φ'} {v' : Fin F.P₀.g → (epsR K' ⟶ Q.A)}
  {basis : IsLieBasis v'} {ψ : Q.A.left ⟶ F.P₀.A.left}

local notation "F₁" => (GenFib.mk (withDim Q (Out.PolAV.g (GenFib.P₀ F)) hd) φ' fib v' basis : GenFib P')

theorem isCoord_over (hξ : IsGrpPullback P'.A P.A (spMap (RingOfIntegers.mapRingHom j)) ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i))
    {u : epsR (𝓞 K) ⟶ P.A} {c : Fin F.P₀.g → K} (hc : F.IsCoord u c) {u' : epsR (𝓞 K') ⟶ P'.A}
    (hu : IsVecOver (RingOfIntegers.mapRingHom j) ξ u u') : (F₁).IsCoord u' (fun i => j (c i)) := by
  obtain ⟨ht, x, hx, hc⟩ := hc
  obtain ⟨x', hx', -⟩ := existsUnique_isVecOver fib.2.1.1 u'
  have h₁ : IsVecOver (j.comp (algebraMap (𝓞 K) K)) (ψ ≫ F.φ) u x' := by
    rw [w, ← algebraMap_comp_mapRingHom]
    exact vec_comp hu hx'
  have h₂ : IsVecOver j ψ x x' := (PolFibre.vec_iff F.fib.2.1.1 hψ.1.w hx).2 h₁
  have h₃ : IsLieComb (fun i => j (c i)) v' x' := Chart.comb_baseChange j hψ hc hv h₂
  exact ⟨hu.isTangent hξ ht, x', hx', h₃⟩

theorem image_subset_lieLat (hξ : IsGrpPullback P'.A P.A (spMap (RingOfIntegers.mapRingHom j)) ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i))
    {c : Fin F.P₀.g → K} (hc : c ∈ F.lieLat) : (fun i => j (c i)) ∈ (F₁).lieLat := by
  obtain ⟨u, hu⟩ := ((_root_.GlobalTheory.CM.integral_tangent_coordinates K P F).2.2.2.2.1 c).1 hc
  obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hξ.1 u
  exact Submodule.subset_span ⟨u', isCoord_over hξ hψ w hv hu hu'⟩

theorem exists_pow_smul_mem {O R k : Type} [CommRing O] [CommRing R] [Field k] [Algebra O R] [Algebra R k] [Algebra O k]
    [IsScalarTower O R k] (r : O) [IsLocalization.Away r R] {n : ℕ} (N : Submodule O (Fin n → k))
    (M : Fin n → Fin n → k) (hM : ∀ i, ∃ l : ℕ, r ^ l • M i ∈ N) (a : Fin n → R) :
    ∃ l : ℕ, r ^ l • (∑ i, algebraMap R k (a i) • M i) ∈ N := by
  have key : ∀ i, ∃ l : ℕ, r ^ l • (algebraMap R k (a i) • M i) ∈ N := fun i => by
    obtain ⟨l, hl⟩ := hM i
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj r (a i)
    refine ⟨m + l, ?_⟩
    have e : r ^ (m + l) • (algebraMap R k (a i) • M i) = b • (r ^ l • M i) := by
      have hb' := congrArg (algebraMap R k) hb
      simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hb'
      rw [← algebraMap_smul k (r ^ (m + l)), ← algebraMap_smul k b, ← algebraMap_smul k (r ^ l), smul_smul, smul_smul,
        ← hb', map_pow, map_pow]
      congr 1
      ring
    rw [e]
    exact N.smul_mem _ hl
  choose l hl using key
  refine ⟨∑ i, l i, ?_⟩
  rw [Finset.smul_sum]
  refine N.sum_mem fun i _ => ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [hm, pow_add, mul_smul]
  exact N.smul_mem _ (hl i)

theorem lieLat_eq_span (hB : Out.PolBaseChangeSt) (hξ : IsPolFibre (RingOfIntegers.mapRingHom j) P P' ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i)) :
    (F₁).lieLat = Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  refine le_antisymm (fun c' hc' => ?_) (Submodule.span_le.2 ?_)
  swap
  · rintro _ ⟨c, hc, rfl⟩
    exact image_subset_lieLat hξ.2.1 hψ w hv hc
  obtain ⟨n, r, M, hr, hM, -, hloc⟩ := _root_.GlobalTheory.CM.LieGlue.exists_cover_lieLat K P F
  have hr' : Ideal.span (Set.range fun i => RingOfIntegers.mapRingHom j (r i)) = ⊤ := by
    have := congrArg (Ideal.map (RingOfIntegers.mapRingHom j)) hr
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hr' c' ?_
  rintro ⟨_, i, rfl⟩
  have h0 : RingOfIntegers.mapRingHom j (r i) ≠ 0 := fun h => (hM i).1 (by
    have := congrArg (algebraMap (𝓞 K') K') h
    exact RingOfIntegers.coe_injective (j.injective (this.trans (by simp))))
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r i)) (powers_le_nonZeroDivisors_of_noZeroDivisors (hM i).1)
  let R' := Localization.subalgebra.ofField K' (Submonoid.powers (RingOfIntegers.mapRingHom j (r i)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors h0)
  let θ : R →+* R' := IsLocalization.Away.map R R' (RingOfIntegers.mapRingHom j) (r i)
  have hθ : θ.comp (algebraMap (𝓞 K) R) = (algebraMap (𝓞 K') R').comp (RingOfIntegers.mapRingHom j) :=
    IsLocalization.map_comp _
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K := (IsScalarTower.algebraMap_eq _ _ _).symm
  have e₂ : (algebraMap R' K').comp (algebraMap (𝓞 K') R') = algebraMap (𝓞 K') K' :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hθ' : (algebraMap R' K').comp θ = j.comp (algebraMap R K) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (r i)) ?_
    rw [RingHom.comp_assoc, hθ, ← RingHom.comp_assoc, e₂, RingHom.comp_assoc, e₁]
    rfl
  obtain ⟨G, κ, hκ⟩ := exists_isPolFibre hB (algebraMap (𝓞 K) R) P
  obtain ⟨G', κ', hκ'⟩ := exists_isPolFibre hB (algebraMap (𝓞 K') R') P'
  obtain ⟨ζ, hζ, hζκ⟩ := PolFibre.cancel (g := algebraMap R K) hκ (by rw [e₁]; exact F.fib)
  obtain ⟨ζ', hζ', hζκ'⟩ := PolFibre.cancel (g := algebraMap R' K') hκ' (by rw [e₂]; exact fib)
  obtain ⟨χ, hχ, hχκ⟩ := PolFibre.cancel (g := θ) hκ (by rw [hθ]; exact PolFibre.comp hξ hκ')
  have hsq : ψ ≫ ζ = ζ' ≫ χ := by
    refine hκ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hζκ, hχκ, w, ← hζκ', Category.assoc]
    · rw [Category.assoc, Category.assoc, hζ.2.1.1.w, hχ.2.1.1.w, ← Category.assoc, ← Category.assoc, hψ.1.w,
        hζ'.2.1.1.w, Category.assoc, Category.assoc, spMap_comp_spMap, spMap_comp_spMap, hθ']
  obtain ⟨e, he, hx⟩ := hloc i R G.A κ ζ
    (IsLocalization.map_units R (⟨r i, Submonoid.mem_powers _⟩ : Submonoid.powers (r i))) hκ.2.1 hζ.2.1 hζκ
  choose x hx hxM using hx
  haveI := G.isAb.comm
  haveI := G'.isAb.comm
  haveI := G.smoothDim
  obtain ⟨e', he', hee'⟩ := exists_isLieBasis_baseChange R R' θ G.A G'.A χ hχ.2.1
    (SmoothOfRelativeDimension.smooth G.g _) _ e he
  choose x' hx' using fun k => (existsUnique_isVecOver hζ'.2.1.1 (e' k)).exists
  have hxM' : ∀ k, IsLieComb ((M i).map j k) v' (x' k) := fun k => by
    refine Chart.comb_baseChange j hψ (hxM k) hv ?_
    refine (PolFibre.vec_iff hζ.2.1.1 hψ.1.w (hx k)).2 ?_
    rw [hsq, ← hθ']
    exact vec_comp (hee' k) (hx' k)
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.CM.LieLoc.lieLat_localization K' P' F₁ R' (Submonoid.powers (RingOfIntegers.mapRingHom j (r i))) G'.A κ' ζ' e' x'
    ((M i).map j) hκ'.2.1 hζ'.2.1 hζκ' he' fun k => ⟨hx' k, hxM' k⟩).2 c' hc'
  have hin := (_root_.GlobalTheory.CM.LieLoc.lieLat_localization K P F R (Submonoid.powers (r i)) G.A κ ζ e x (M i) hκ.2.1 hζ.2.1 hζκ he
    fun k => ⟨hx k, hxM k⟩).1
  rw [ha]
  refine exists_pow_smul_mem (RingOfIntegers.mapRingHom j (r i)) _ _ (fun k => ?_) a
  obtain ⟨_, ⟨l, rfl⟩, hl⟩ := hin k
  refine ⟨l, Submodule.subset_span ⟨_, hl, funext fun t => ?_⟩⟩
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_pow, Matrix.map_apply]
  rfl

theorem eigLat_eq_span (hB : Out.PolBaseChangeSt) (hξ : IsPolFibre (RingOfIntegers.mapRingHom j) P P' ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i))
    {O : Type} [CommRing O] (act : OAct O P.A) (act' : OAct O P'.A)
    (hact : ∀ a, (act'.act a).left ≫ ξ = ξ ≫ (act.act a).left) (τ : O →+* 𝓞 K) :
    (F₁).eigLat act' ((RingOfIntegers.mapRingHom j).comp τ) =
      Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.eigLat act τ : Set (Fin F.P₀.g → K))) := by
  obtain ⟨r, hr, he⟩ := _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat K P F O act
  obtain ⟨r', hr', he'⟩ := _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat K' P' F₁ O act'
  have hL := lieLat_eq_span (fib := fib) (basis := basis) hB hξ hψ w hv
  have key : ∀ a, ∀ c' ∈ (F₁).lieLat, r' a c' = ((LinearMap.toMatrix' (r a)).map j).mulVec c' := fun a c' hc' => by
    rw [hL] at hc'
    induction hc' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨u, hu⟩ := ((_root_.GlobalTheory.CM.integral_tangent_coordinates K P F).2.2.2.2.1 c).1 hc
      obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hξ.2.1.1 u
      have h₁ := hr' a _ _ (isCoord_over (fib := fib) (basis := basis) hξ.2.1 hψ w hv hu hu')
      have h₂ := isCoord_over (fib := fib) (basis := basis) hξ.2.1 hψ w hv (hr a _ _ hu) (u' := u' ≫ act'.act a) (by
        unfold IsVecOver at hu' ⊢
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, hu', Category.assoc])
      refine (((_root_.GlobalTheory.CM.integral_tangent_coordinates K' P' F₁).1 _ h₁.1).unique h₁ h₂).trans (funext fun t => ?_)
      rw [← LinearMap.toMatrix'_mulVec (r a) c]
      exact RingHom.map_mulVec j _ c t
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Matrix.mulVec_add, hx, hy]
    | smul s x _ hx => rw [← algebraMap_smul K' s x, map_smul, Matrix.mulVec_smul, hx]
  have hs : (F.eigLat act τ : Set (Fin F.P₀.g → K)) =
      {c | c ∈ F.lieLat ∧ ∀ a, (LinearMap.toMatrix' (r a)).mulVec c = algebraMap (𝓞 K) K (τ a) • c} := by
    ext c
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, (he τ c).1, LinearMap.toMatrix'_mulVec, algebraMap_smul]
  ext c'
  rw [hs, _root_.GlobalTheory.CM.eigenLattice_baseChange K K' O j F.P₀.g F.lieLat _ _ c' (_root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).1, ← hL, (he' _ c').1]
  refine and_congr_right fun hc' => forall_congr' fun a => ?_
  rw [key a c' hc', ← algebraMap_smul K']
  rfl


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {j : K →+* K'}

theorem exists_genFib_baseChange (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K')))
    (m : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) :
    ∃ (Q : Out.PolAV (Sp K')) (hd : SmoothOfRelativeDimension F.P₀.g Q.A.hom) (φ' : Q.A.left ⟶ T'.t.G.left)
      (fib : IsPolFibre (algebraMap (𝓞 K') K') T'.pol (withDim Q F.P₀.g hd) φ')
      (v' : Fin F.P₀.g → (epsR K' ⟶ Q.A)) (basis : IsLieBasis v'),
      (∀ τ : 𝓞 E →+* 𝓞 K, (GenFib.mk (withDim Q F.P₀.g hd) φ' fib v' basis : GenFib T'.pol).eigLat T'.t.act
          ((RingOfIntegers.mapRingHom j).comp τ) =
        Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)))) ∧
      ∀ (u : epsR (𝓞 K) ⟶ T.t.G) (c : Fin F.P₀.g → K), F.IsCoord u c → ∀ u' : epsR (𝓞 K') ⟶ T'.t.G,
        IsVecOver (RingOfIntegers.mapRingHom j) m.φ u u' →
        (GenFib.mk (withDim Q F.P₀.g hd) φ' fib v' basis : GenFib T'.pol).IsCoord u' (fun i => j (c i)) := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hB : Out.PolBaseChangeSt := hL.polBaseChange
  have hdT : SmoothOfRelativeDimension T.g T'.t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m.cart.1 T.dim
  have hξ : IsPolFibre (RingOfIntegers.mapRingHom j) T.pol T'.pol m.φ :=
    ⟨H1.dim_unique _ T'.dim hdT (eSec T'.t.G (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 K'))), m.cart,
      (PAT.exists_of_sabMap E H _ _ _ T T'.t m).2⟩
  obtain ⟨F'⟩ := GenFib.nonempty_of_baseChange hB K' T'.pol
  have hg : F'.P₀.g = F.P₀.g := F'.fib.1.trans (hξ.1.trans F.fib.1.symm)
  have hd : SmoothOfRelativeDimension F.P₀.g F'.P₀.A.hom := hg ▸ F'.P₀.smoothDim
  have fib : IsPolFibre (algebraMap (𝓞 K') K') T'.pol (withDim F'.P₀ F.P₀.g hd) F'.φ := ⟨hg.symm.trans F'.fib.1, F'.fib.2⟩
  obtain ⟨ψ, hψ, w⟩ := PolFibre.cancel (g := j) F.fib (PolFibre.comp hξ fib)
  have := F.P₀.isAb.comm
  have := F'.P₀.isAb.comm
  have := F.P₀.smoothDim
  obtain ⟨v', basis, hv⟩ := exists_isLieBasis_baseChange K K' j F.P₀.A F'.P₀.A ψ hψ.2.1
    (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
  refine ⟨F'.P₀, hd, F'.φ, fib, v', basis, fun τ => ?_, fun u c hc u' hu => ?_⟩
  · exact eigLat_eq_span hB hξ hψ.2.1 w hv T.t.act T'.t.act m.act τ
  · exact isCoord_over hξ.2.1 hψ.2.1 w hv hc hu

end GlobalTheory.CM.LieSpanBaseChange
end

noncomputable section
namespace GlobalTheory.CM.LieSpanBaseChange

open GlobalTheory.CM.LieBaseChange GlobalTheory.CM.IntCoord

theorem eigLat_image_le_span_diff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G))
    (f' : Fin n → (A'.t.G ⟶ B'.t.G)) (g' : Fin n → (B'.t.G ⟶ A'.t.G)),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) → (∀ i, Serre.IsLinearHom A'.t.act B'.t.act (f' i)) →
    (∀ i, Serre.IsLinearHom B'.t.act A'.t.act (g' i)) → (∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) →
    ∏ i, (g' i ≫ f' i) = 𝟙 B'.t.G →
    ∀ (FA : GenFib A.pol) (FB : GenFib B.pol) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
    (∀ i, FA.IsDiffOf FB (f i) (M i)) → ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ w ∈ FB.eigLat B.t.act τ,
    (fun k => j (w k)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB n f f' g' _ hf' hg' hff' hid FA FB M hM τ w hw
  obtain ⟨QA, hdA, φA, fibA, vA, bA, hA1, hA2⟩ := exists_genFib_baseChange A A' mA FA
  obtain ⟨QB, hdB, φB, fibB, vB, bB, hB1, hB2⟩ := exists_genFib_baseChange B B' mB FB
  let F₁A : GenFib A'.pol := GenFib.mk (withDim QA FA.P₀.g hdA) φA fibA vA bA
  let F₁B : GenFib B'.pol := GenFib.mk (withDim QB FB.P₀.g hdB) φB fibB vB bB
  have hcB := _root_.GlobalTheory.CM.integral_tangent_coordinates K' _ F₁B
  choose M' hM' using fun i =>
    ((DiffCoord.existsUnique_isDiffOf K' A'.pol F₁A B'.pol F₁B (f' i) (hf' i).isMonHom).1).exists
  choose N' hN' using fun i =>
    ((DiffCoord.existsUnique_isDiffOf K' B'.pol F₁B A'.pol F₁A (g' i) (hg' i).isMonHom).1).exists
  set S := Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) with hSdef
  have hjadd : ∀ {m : ℕ} (x y : Fin m → K), (fun k => j ((x + y) k)) = (fun k => j (x k)) + (fun k => j (y k)) :=
    fun x y => funext fun k => by simp
  have hjsmul : ∀ {m : ℕ} (r : 𝓞 K) (x : Fin m → K),
      (fun k => j ((r • x) k)) = (RingOfIntegers.mapRingHom j r) • (fun k => j (x k)) :=
    fun r x => funext fun k => by
      rw [← algebraMap_smul K r x, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, ← algebraMap_smul K',
        smul_eq_mul]
      rfl
  have hcomp : ∀ i, ∀ e ∈ FA.eigLat A.t.act τ, M' i (fun k => j (e k)) = fun k => j (M i e k) := by
    intro i e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, -⟩ := hx
      obtain ⟨u', hu', -⟩ := existsUnique_isVecOver mA.cart.1 u
      have h1 := hM' i u' _ (hA2 u x hu u' hu')
      have h2 := hB2 (u ≫ f i) (M i x) (hM i u x hu) (u' ≫ f' i) (by
        unfold IsVecOver at hu' ⊢
        rw [Over.comp_left, Over.comp_left, Category.assoc, hff' i, ← Category.assoc, hu', Category.assoc])
      exact (hcB.1 _ h1.1).unique h1 h2
    | zero =>
      have h0 : (fun k => j ((0 : Fin FA.P₀.g → K) k)) = 0 := funext fun k => by simp
      rw [h0, map_zero, map_zero]
      funext k
      simp
    | add x y _ _ hx hy =>
      rw [hjadd, map_add (f := _), hx, hy, map_add (f := _), hjadd]
    | smul r x _ hx =>
      rw [hjsmul, ← algebraMap_smul K' (RingOfIntegers.mapRingHom j r), map_smul, hx, algebraMap_smul,
        ← algebraMap_smul K r x, map_smul, algebraMap_smul, hjsmul]
  have hS : ∀ i, ∀ x ∈ Submodule.span (𝓞 K') ((fun (c : Fin FA.P₀.g → K) k => j (c k)) ''
      (FA.eigLat A.t.act τ : Set (Fin FA.P₀.g → K))), M' i x ∈ S := by
    intro i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      rw [hcomp i e he]
      exact Submodule.subset_span ⟨M i e, ⟨i, e, he, rfl⟩, rfl⟩
    | zero =>
      rw [map_zero]
      exact S.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact S.add_mem hx hy
    | smul s x _ hx =>
      rw [← algebraMap_smul K' s x, map_smul, algebraMap_smul]
      exact S.smul_mem s hx
  have hkey : F₁B.eigLat B'.t.act ((RingOfIntegers.mapRingHom j).comp τ) ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro c' ⟨u', hu', heig⟩
    have hN'mem : ∀ i, N' i c' ∈ F₁A.eigLat A'.t.act ((RingOfIntegers.mapRingHom j).comp τ) := fun i =>
      Indep.map_eigLat_le (hg' i).comm (hN' i) _
        (Submodule.mem_map_of_mem (f := (N' i).restrictScalars (𝓞 K')) (Submodule.subset_span ⟨u', hu', heig⟩))
    have hs : ∀ i, F₁B.IsCoord (u' ≫ (g' i ≫ f' i)) (M' i (N' i c')) := fun i => by
      rw [← Category.assoc]
      exact hM' i _ _ (hN' i _ _ hu')
    have hprod : ∀ s : Finset (Fin n),
        F₁B.IsCoord (u' ≫ ∏ i ∈ s, (g' i ≫ f' i)) (∑ i ∈ s, M' i (N' i c')) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.sum_empty, comp_one]
        exact isCoord_one F₁B
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
        exact isCoord_mul F₁B (hs a) ih
    have h1 := hprod Finset.univ
    rw [hid, Category.comp_id] at h1
    have heq : c' = ∑ i, M' i (N' i c') := (hcB.1 _ hu'.1).unique hu' h1
    rw [heq]
    refine S.sum_mem fun i _ => hS i _ ?_
    rw [← hA1 τ]
    exact hN'mem i
  have hw' : (fun k => j (w k)) ∈ F₁B.eigLat B'.t.act ((RingOfIntegers.mapRingHom j).comp τ) := by
    rw [hB1 τ]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  exact hkey hw'

end GlobalTheory.CM.LieSpanBaseChange
end
