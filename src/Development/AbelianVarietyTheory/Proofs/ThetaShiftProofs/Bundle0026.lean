module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LePreimageOfUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecGroup

section General

variable {S : Scheme.{0}} {G T T' : Over S}

theorem left_mul_of_comp [GrpObj G] (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom) {a b : T ⟶ G} {a' b' : T' ⟶ G}
    (ha : a'.left = r ≫ a.left) (hb : b'.left = r ≫ b.left) : (a' * b').left = r ≫ (a * b).left := by
  have e₁ : a' = Over.homMk r hr ≫ a := Over.OverMorphism.ext ha
  have e₂ : b' = Over.homMk r hr ≫ b := Over.OverMorphism.ext hb
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl

theorem left_one [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem map_zero_eq_one {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v') :
    x 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem ext_of_generic {A K : Type} [CommRing A] [Field K] {j : A →+* K} (hj : Function.Injective j)
    [IsSeparated G.hom] {p : Sp A ⟶ S} {a b : Over.mk p ⟶ G} (h : spMap j ≫ a.left = spMap j ≫ b.left) : a = b := by
  have : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have : IsDomain A := hj.isDomain j
  exact Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp A) G.hom ((Over.w a).trans (Over.w b).symm) (spMap j) h)

theorem le_preimage_of_unit {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have h₀ : spMap ρ (⊥ : PrimeSpectrum K) ∈ x ⁻¹ᵁ U := h (x := (⊥ : PrimeSpectrum K)) trivial
  have hs : (show PrimeSpectrum A from p) ⤳ (show PrimeSpectrum A from spMap ρ (⊥ : PrimeSpectrum K)) := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun s hs => ?_
    change ρ s ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    by_contra hne
    exact (show PrimeSpectrum A from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (hρ s hne))
  exact hs.mem_open (x ⁻¹ᵁ U).isOpen h₀

theorem isFrm_map {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (L : LB X) (x : Sp A ⟶ X) (τ : L.ι → A) (h : IsFrm L x τ) :
    IsFrm L (spMap ρ ≫ x) (fun j => ρ (τ j)) := by
  refine ⟨fun j hj => (h.1 j (le_preimage_of_unit ρ hρ x _ hj)).map ρ, fun j j' hj => ?_⟩
  have hx := le_preimage_of_unit ρ hρ x _ hj
  rw [HolHom.valR_spMap ρ x _ hx, ← map_mul, ← h.2 j j' hx]

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y} {Γ : Germs} (Ψ : SpecPts Φ Γ)
  {w : ℂ} (hw : Ψ.T < w.im)

theorem val_base :
    spMap (Γ.R w).val.toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = y := by
  rw [← Category.assoc, spMap_comp_spMap]
  exact Ψ.yT_gen

theorem ev_base :
    spMap (Γ.ev w).toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = Ψ.yw w := by
  rw [← Category.assoc, spMap_comp_spMap, Ψ.yw_eq w hw]
  congr 2
  exact RingHom.ext fun s => Γ.ev_eq Ψ.T w hw s

theorem xt_add (v v' : A.V) : Ψ.xt w hw (v + v') = Ψ.xt w hw v * Ψ.xt w hw v' := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.add]
  exact left_mul_of_comp (T' := Over.mk y) _ (val_base Ψ hw) (Ψ.xt_gen w hw v).symm (Ψ.xt_gen w hw v').symm

theorem xt_act (e : 𝓞 E) (v : A.V) : Ψ.xt w hw (A.actV e v) = Ψ.xt w hw v ≫ t.act.act e := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.lin, Over.comp_left, Over.comp_left, ← Ψ.xt_gen w hw v, Category.assoc]

include hw

theorem pi_add (v v' : A.V) : Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v' := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_add]
  exact (left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (ev_base Ψ hw) (Ψ.pi_eq w hw v) (Ψ.pi_eq w hw v')).symm

theorem pi_act (e : 𝓞 E) (v : A.V) : Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ t.act.act e := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_act, Over.comp_left, Over.comp_left, Ψ.pi_eq w hw, Category.assoc]

theorem pi_frm (v : A.V) : IsFrm t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v) := by
  rw [Ψ.pi_eq w hw]
  exact isFrm_map (Γ.ev w).toRingHom (Γ.unit w) _ _ _ (Ψ.τt_frm w hw v)

theorem pi_rig (j : t.PP.L.ι) (hj : ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ t.PP.L.U j) :
    Ψ.fr w j 0 = valAt' (Ψ.yw w) ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
  rw [Ψ.pi_eq w hw] at hj
  have h₁ : ⊤ ≤ (Ψ.xt w hw 0).left ⁻¹ᵁ t.PP.L.U j := le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ hj
  have h₂ : ⊤ ≤ (Φ.x 0).left ⁻¹ᵁ t.PP.L.U j := by
    rw [← Ψ.xt_gen w hw 0]
    exact fun p _ => h₁ (x := spMap (Γ.R w).val.toRingHom p) trivial
  have h₃ : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ
      (t.PP.L.pull (eSec t.G)).U (fun _ => j) := by
    rw [map_zero_eq_one _ (xt_add Ψ hw), left_one] at h₁
    exact fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  have h₄ : Ψ.τt w 0 j = valR (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)
      ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
    refine Subtype.ext ?_
    rw [Ψ.τt_gen w hw 0 j h₁, Φ.rig j h₂]
    exact (congrArg (fun q => valR q _ _) (val_base Ψ hw).symm).trans
      (HolHom.valR_spMap (Γ.R w).val.toRingHom _ _ h₃ _)
  rw [SpecPts.fr, h₄, HolHom.valAt'_eq_valR, ← ev_base Ψ hw]
  exact (HolHom.valR_spMap (Γ.ev w).toRingHom _ _ h₃ _).symm

omit hw

theorem specPts_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ w : ℂ, Ψ.T < w.im → (∀ v v', Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v') ∧ (∀ (e : 𝓞 E) v, Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ o.t.act.act e) ∧ (∀ v, IsFrm o.t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v)) ∧ ∀ j, ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j 0 = valAt' (Ψ.yw w) ((o.t.PP.L.pull (eSec o.t.G)).U (fun _ => j)) (o.t.PP.rig.s (fun _ => j)).val :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ _ hw =>
    ⟨pi_add Ψ hw, pi_act Ψ hw, pi_frm Ψ hw, pi_rig Ψ hw⟩

end GlobalTheory.SpecGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRealSpanPeriodsOfCharacterKernel
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.PeriodSpan

theorem eq_of_exp_mul_eq {a b : ℂ} (H : ∀ s : ℂ, Complex.exp (s * a) = Complex.exp (s * b)) :
    a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h1 := H (Real.pi * Complex.I / (a - b))
  have h2 : Complex.exp (Real.pi * Complex.I / (a - b) * a - Real.pi * Complex.I / (a - b) * b)
      = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [← mul_sub, div_mul_cancel₀ _ hd, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem exists_block_solution {g : ℕ} (S : Finset (Fin g)) (A : Matrix (Fin g) (Fin g) ℝ)
    (hA : A.PosDef) (y : Fin g → ℝ) :
    ∃ b : Fin g → ℝ, (∀ k ∈ S, b k = 0) ∧ ∀ k ∉ S, A.mulVec b k = y k := by
  classical
  let T : (Fin g → ℝ) →ₗ[ℝ] (Fin g → ℝ) :=
    LinearMap.pi fun k => if k ∈ S then LinearMap.proj k
      else (LinearMap.proj k).comp A.mulVecLin
  have hT : ∀ b k, T b k = if k ∈ S then b k else A.mulVec b k := by
    intro b k
    by_cases hk : k ∈ S <;> simp [T, hk]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    have hpos := hA.dotProduct_mulVec_pos hb0
    have : star b ⬝ᵥ A.mulVec b = 0 := by
      unfold dotProduct
      refine Finset.sum_eq_zero fun k _ => ?_
      have h1 := hT b k
      rw [hb] at h1
      by_cases hk : k ∈ S
      · simp only [hk, if_true, Pi.zero_apply] at h1
        simp [← h1]
      · simp only [hk, if_false, Pi.zero_apply] at h1
        simp [← h1]
    exact hpos.ne' this
  obtain ⟨b, hb⟩ := LinearMap.surjective_of_injective hinj
    (fun k => if k ∈ S then 0 else y k)
  refine ⟨b, fun k hk => ?_, fun k hk => ?_⟩
  · have := hT b k
    rw [hb] at this
    simpa [hk] using this.symm
  · have := hT b k
    rw [hb] at this
    simpa [hk] using this.symm

theorem mem_span_periods : ∀ (g n : ℕ) (S : Finset (Fin g)) (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (ℓ : Fin g → (Fin g → ℂ) →ₗ[ℂ] ℂ), 0 < n → (τ.map Complex.im).PosDef → (∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧ h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) → (∀ k ∈ S, ∀ k' ∈ S, ∀ s : ℂ, Complex.exp (ℓ k (s • p (Pi.single (.inl k') 1))) = eTwoPi (n * s * if k' = k then 1 else 0)) → (∀ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) → ∀ k ∈ S, Complex.exp (ℓ k (p u)) = 1) → ∀ z : Fin g → ℂ, (∀ k ∈ S, ℓ k z = 0) → z ∈ Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u} := by
  classical
  intro g n S h τ p ℓ hn hτ hp hℓ hu z hz
  set R := Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u}
    with hR
  set e : Fin g → Fin g → ℂ := fun k => p (Pi.single (.inl k) 1) with he
  set f : Fin g → Fin g → ℂ := fun k => p (Pi.single (.inr k) 1) with hf
  have hhe : ∀ k, h.mulVec (e k) = Pi.single k 1 := fun k => (hp k).1
  have hhf : ∀ k, h.mulVec (f k) = τ.mulVec (Pi.single k 1) := fun k => (hp k).2
  have hinj : Function.Injective h.mulVec := by
    have hM : h * (Matrix.of fun i k => e k i) = 1 := by
      ext i k
      have := congrFun (hhe k) i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
        using this
    have hM' := mul_eq_one_comm.mp hM
    intro x y hxy
    have := congrArg (Matrix.of fun i k => e k i).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hM'] using this
  have hℓe : ∀ k ∈ S, ∀ k' ∈ S, ℓ k (e k') =
      2 * Real.pi * Complex.I * n * if k' = k then 1 else 0 := by
    intro k hk k' hk'
    refine eq_of_exp_mul_eq fun s => ?_
    have := hℓ k hk k' hk' s
    rw [map_smul, smul_eq_mul, eTwoPi] at this
    rw [he]
    refine this.trans ?_
    congr 1
    ring
  have hre : ∀ r ∈ R, ∀ k ∈ S, (ℓ k r).re = 0 := by
    intro r hr k hk
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu', rfl⟩ := hx
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (hu u hu' k hk)
      rw [hm]
      simp
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx =>
      rw [← Complex.coe_smul, map_smul]
      simp [hx]
  have heR : ∀ k, e k ∈ R := fun k =>
    Submodule.subset_span ⟨Pi.single (.inl k) 1, fun k' _ => by simp, rfl⟩
  have hfR : ∀ k ∉ S, f k ∈ R := fun k hk =>
    Submodule.subset_span ⟨Pi.single (.inr k) 1, fun k' hk' => by
      have : k' ≠ k := fun e => hk (e ▸ hk')
      simp [this], rfl⟩
  obtain ⟨b, hbS, hb⟩ := exists_block_solution S _ hτ fun k => (h.mulVec z k).im
  set c : Fin g → ℂ := h.mulVec z - τ.mulVec fun k => (b k : ℂ) with hc
  have hcim : ∀ k ∉ S, (c k).im = 0 := by
    intro k hk
    have := hb k hk
    simp only [hc, Pi.sub_apply, Complex.sub_im]
    rw [← this]
    simp [Matrix.mulVec, dotProduct]
  have hzeq : z = ∑ k, (b k : ℂ) • f k + ∑ k, c k • e k := by
    apply hinj
    have h1 : ∑ k, (b k : ℂ) • (Pi.single k 1 : Fin g → ℂ) = fun k => (b k : ℂ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : ∑ k, c k • (Pi.single k 1 : Fin g → ℂ) = c := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hhe, hhf, h2]
    simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum, h1]
    rw [hc]; abel
  set r : Fin g → ℂ := ∑ k, (b k : ℂ) • f k + ∑ k, ((c k).re : ℂ) • e k with hr
  have hrR : r ∈ R := by
    refine R.add_mem (R.sum_mem fun k _ => ?_) (R.sum_mem fun k _ => ?_)
    · by_cases hk : k ∈ S
      · simp [hbS k hk]
      · rw [Complex.coe_smul]; exact R.smul_mem _ (hfR k hk)
    · rw [Complex.coe_smul]; exact R.smul_mem _ (heR k)
  have hzr : z = r + ∑ k, (((c k).im : ℂ) * Complex.I) • e k := by
    rw [hr, add_assoc, ← Finset.sum_add_distrib]
    simp only [← add_smul, Complex.re_add_im]
    exact hzeq
  have him : ∀ k, (c k).im = 0 := by
    intro k
    by_cases hk : k ∈ S
    · have h0 := hz k hk
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hzr, map_add (f := _), map_sum, Finset.sum_eq_single k] at h0
      · have h1 := congrArg Complex.re h0
        rw [map_smul, hℓe k hk k hk, Complex.add_re, hre r hrR k hk] at h1
        simpa [Real.pi_ne_zero, hn.ne'] using h1
      · intro k' _ hne
        by_cases hk' : k' ∈ S
        · rw [map_smul, hℓe k hk k' hk']
          simp [hne]
        · simp [hcim k' hk']
      · simp
    · exact hcim k hk
  rw [hzr]
  simpa [him] using hrR

end GlobalTheory.PeriodSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RepTransport
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj

namespace GlobalTheory.FibreFrame

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {X Y Z : Scheme.{0}} {L : LB Z} {m : ℕ}

theorem le_wchart {π : X ⟶ Z} {q : Sp R ⟶ X} {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem sval_spMap {π : X ⟶ Z} (s : SecP L π m) (ρ : R →+* R') (q : Sp R ⟶ X) {j : L.ι}
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) : ArcPts.sval s (spMap ρ ≫ q) j = ρ (ArcPts.sval s q j) :=
  HolHom.valR_spMap ρ q _ (le_wchart h) _

theorem exists_pull {π : X ⟶ Z} (s : SecP L π m) (h : Y ⟶ X) {π' : Y ⟶ Z} (e : h ≫ π = π') :
    ∃ s' : SecP L π' m, (∀ j (le : LB.wchart L (fun _ : Fin 1 => π') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) j),
        s'.f j = (Y.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
        ArcPts.sval s' q j = ArcPts.sval s (q ≫ h) j := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : Fin 1 => π) (fun _ => (m : ℤ)) s h, fun _ _ => rfl, fun R _ q j hj => ?_⟩
  exact (HolHom.valR_res q _ _ (le_wchart hj)).trans (HolHom.valR_comp q h _ _).symm

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, Conv.valR_spMap_top]

def comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((comb p r σ).f j) = ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, comb, map_sum, map_mul]

theorem sval_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (r : Fin n → K) (σ : Fin n → SecP L π m) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (comb p r σ : SecP L π m) q j = ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  exact valR_comb p r σ f q hq (fun _ => j) (le_wchart h)

theorem ext_sval {π : X ⟶ Z} {s s' : SecP L π m}
    (h : ∀ (R : Type) [CommRing R] (q : Sp R ⟶ X) (j : L.ι), ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
      ArcPts.sval s q j = ArcPts.sval s' q j) (j : Fin 1 → L.ι) : s.f j = s'.f j := by
  obtain ⟨j, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) hx
  obtain ⟨q, hq, hv⟩ := Conv.exists_point_of_ringHom hV (RingHom.id _)
  have hle' : V ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) := hle
  have e := h _ q j fun z hz => LB.wchart_le L (fun _ : Fin 1 => π) (fun _ => j) 0 (hle' (hq hz))
  have e1 := (hv _).symm.trans (HolHom.valR_res q hle' (s.f fun _ => j) hq)
  have e2 := (hv _).symm.trans (HolHom.valR_res q hle' (s'.f fun _ => j) hq)
  exact X.presheaf.germ_ext V hxV (homOfLE hle') (homOfLE hle') (e1.trans (e.trans e2.symm))

def Rep {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) : Prop :=
  ∀ (R : Type) [CommRing R] (f : K →+* R) (q : Sp R ⟶ X) (j : L.ι), q ≫ p = spMap f → ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
    ArcPts.sval s q j = ∑ i, f (c i) * ArcPts.sval (σ i) q j

theorem rep_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (c : Fin n → K) :
    Rep p σ (comb p c σ) c := fun _ _ f q _ hq h => sval_comb p c σ f q hq h

theorem rep_iff {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) :
    Rep p σ s c ↔ ∀ j, s.f j = (comb p c σ).f j := by
  refine ⟨fun H => ext_sval fun R _ q j hj => ?_, fun H R _ f q j hq hj => ?_⟩
  · have hq : q ≫ p = spMap (Spec.preimage (q ≫ p)).hom := (Spec.map_preimage _).symm
    exact (H R _ q j hq hj).trans (sval_comb p c σ _ q hq hj).symm
  · exact (congrArg (valR q _) (H _)).trans (sval_comb p c σ f q hq hj)

theorem rep_transport {π : X ⟶ Z} {p : X ⟶ Sp K} {n : ℕ} {σ : Fin n → SecP L π m} (e : Y ≅ X) {π' : Y ⟶ Z}
    {p' : Y ⟶ Sp K} (hπ : e.hom ≫ π = π') (hp : e.hom ≫ p = p') {σ' : Fin n → SecP L π' m}
    (hσ : ∀ i (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
      ArcPts.sval (σ' i) q j = ArcPts.sval (σ i) (q ≫ e.hom) j)
    (H : ∀ s, ∃! c, Rep p σ s c) (s' : SecP L π' m) : ∃! c, Rep p' σ' s' c := by
  subst hπ hp
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (π' := π) (e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ p) σ' s' c ↔ Rep p σ s c := fun c => by
    constructor
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.inv) ≫ e.hom ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      rw [hs R q j hj, h R f _ j (by simpa using hq) hj']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσ i R _ j hj', Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.hom) ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      have := h R f (q ≫ e.hom) j (by simpa using hq) hj'
      rw [hs R _ j hj', Category.assoc, e.hom_inv_id, Category.comp_id] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ i R _ j hj]
  simp only [key]
  exact H s


open Out in
theorem exists_frame (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ)
    (hn : 1 ≤ n) (x : S) : ∃ V : S.Opens, x ∈ V ∧ ∃ (N : ℕ) (β : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S),
      ⊤ ≤ y ⁻¹ᵁ V → Fin N → SecP P.L (pullback.fst P.A.hom y) n),
      (∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (R' : Type) [CommRing R'] (y' : Sp R' ⟶ S)
        (hy' : ⊤ ≤ y' ⁻¹ᵁ V) (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (q' : Sp C ⟶ pullback P.A.hom y')
        (i : Fin N) (j : P.L.ι), q ≫ pullback.fst _ _ = q' ≫ pullback.fst _ _ →
        ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j → ArcPts.sval (β R y hy i) q j = ArcPts.sval (β R' y' hy' i) q' j) ∧
      ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (s : SecP P.L (pullback.fst P.A.hom y) n),
        ∃! c, Rep (pullback.snd P.A.hom y) (β R y hy) s c := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn x
  let W := overRes (T := baseOver S) V
  have key : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ (k : pullback P.A.hom y ⟶ (W ⊗ P.A).left) (β : Fin (n ^ P.g) → SecP P.L (pullback.fst P.A.hom y) n),
        k ≫ (snd W P.A).left = pullback.fst _ _ ∧
        (∀ i (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (j : P.L.ι),
          ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j →
          ArcPts.sval (β i) q j = ArcPts.sval (m := n) (p := (snd W P.A).left) (b i) (q ≫ k) j) ∧
        ∀ s, ∃! c, Rep (pullback.snd P.A.hom y) β s c := by
    intro R _ y hy
    let t : Sp R ⟶ W.left := IsOpenImmersion.lift V.ι y (by
      rintro _ ⟨z, rfl⟩
      exact V.range_ι.ge (hy (x := z) trivial))
    have ht : (baseAt t).hom = y := by
      show t ≫ V.ι ≫ 𝟙 _ = y
      rw [Category.comp_id]
      exact IsOpenImmersion.lift_fac _ _ _
    have hp : IsPullback (pullback.snd P.A.hom y) (pullback.fst P.A.hom y) (baseAt t).hom P.A.hom :=
      ht ▸ (IsPullback.of_hasPullback P.A.hom y).flip
    let e : pullback P.A.hom y ≅ (baseAt t ⊗ P.A).left := hp.isoPullback
    have e₁ : e.hom ≫ (snd (baseAt t) P.A).left = pullback.fst _ _ := hp.isoPullback_hom_snd
    have e₂ : e.hom ≫ (fst (baseAt t) P.A).left = pullback.snd _ _ := hp.isoPullback_hom_fst
    have e₃ : (homAt t ▷ P.A).left ≫ (snd W P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    choose b' hb0 hb' using fun i => exists_pull (π := (snd W P.A).left) (m := n) (b i) (homAt t ▷ P.A).left e₃
    choose β _ hβ using fun i => exists_pull (b' i) e.hom e₁
    obtain ⟨hli, hsp⟩ := hb R t b' (fun i j => hb0 i j _)
    refine ⟨e.hom ≫ (homAt t ▷ P.A).left, β, (Category.assoc _ _ _).trans ((congrArg _ e₃).trans e₁), fun i C _ q j hj => ?_,
      rep_transport (p := (fst (baseAt t) P.A).left) e e₁ e₂ hβ fun s => ?_⟩
    · rw [hβ i C q j hj, hb' i C _ j (by rw [Category.assoc, e₁]; exact hj), Category.assoc]
    have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    have key : ∀ c : Fin (n ^ P.g) → R, Rep (fst (baseAt t) P.A).left b' s c ↔
        ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
      have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
          (comb (K := R) (fst (baseAt t) P.A).left c b').f j := fun j => by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
      rw [rep_iff]
      exact ⟨fun h => Subtype.ext (funext fun j => (ev j).trans (h j).symm),
        fun h j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
    choose a ha using fun i => bij.2 (r i)
    obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) = r := funext ha
    refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i
  choose k β hk hβ hr using key
  refine ⟨V, hV, _, β, fun R _ y hy R' _ y' hy' C _ q q' i j hq hj => ?_, hr⟩
  have hm : Mono (snd W P.A).left := by
    have : Mono W.hom := inferInstanceAs (Mono (V.ι ≫ 𝟙 S))
    exact inferInstanceAs (Mono (pullback.snd W.hom P.A.hom))
  rw [hβ R y hy i C q j hj, hβ R' y' hy' i C q' j (hq ▸ hj)]
  congr 1
  rw [← cancel_mono (snd W P.A).left, Category.assoc, Category.assoc, hk, hk, hq]

end GlobalTheory.FibreFrame
end
end

