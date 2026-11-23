module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeFunctorIsSheafZariskiStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ), Presieve.IsSheaf Scheme.zariskiTopology (GlobalTheory.HilbAff.functor A B r) := by
  first | (exact @GlobalTheory.HilbAff.isSheaf_functor) | (exact GlobalTheory.HilbAff.isSheaf_functor) | (intros; apply GlobalTheory.HilbAff.isSheaf_functor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhat
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.FourMem

theorem eventually_invariant {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x := by
    have h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact h3.eventually h1
  filter_upwards [h1, h2] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · rw [← ht' _ hx', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem four_mem_SB : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  intro X _ _ _ _ h μ _ e he φ hφ
  haveI := h.grp
  haveI := h.t2
  haveI := h.lc
  haveI := h.sc
  obtain ⟨K, hK, hKm⟩ := he.big _ (eventually_invariant hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2) :=
        he.lc.prodMk (he.lc.comp_continuous (continuous_const.prodMk continuous_snd))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold four
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t
    have h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x) := by
      intro x
      rw [ht, he.symm y (x + t), he.add, he.symm x y]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold four
    rw [sub_mul, h1, one_mul, sub_self]

end GlobalTheory.KSp.FourMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardResidueFieldLocalOrderUnitaryProd
section
noncomputable section

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem card_residueField_prod_any : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl

end GlobalTheory.UnitLemma.ResDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanZero
variable {T : Type 1} [Category.{0} T]

def cyc (C : T ⥤ AbCx) (i j : ℤ) : T ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of ((C.obj U).d i j).hom.ker
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨(C.map f).f i x.1, by
        have e := ConcreteCategory.congr_hom ((C.map f).comm i j) x.1
        simp only [ConcreteCategory.comp_apply] at e
        change (C.obj V).d i j ((C.map f).f i x.1) = 0
        rw [e, show (C.obj U).d i j x.1 = 0 from x.2, map_zero]⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

def incl (C : T ⥤ AbCx) (i j : ℤ) : cyc C i j ⟶ term C i where
  app U := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  naturality U V f := by ext x; rfl

def dN (C : T ⥤ AbCx) (i j : ℤ) : term C i ⟶ term C j where
  app U := (C.obj U).d i j
  naturality U V f := (C.map f).comm i j

def pN (C : T ⥤ AbCx) (i j k : ℤ) : term C i ⟶ cyc C j k where
  app U := AddCommGrpCat.ofHom
    { toFun := fun y => ⟨(C.obj U).d i j y, by
        change (C.obj U).d j k ((C.obj U).d i j y) = 0
        exact ConcreteCategory.congr_hom ((C.obj U).d_comp_d i j k) y⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  naturality U V f := by
    ext y
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((C.map f).comm i j) y

end GlobalTheory.CartanZero

namespace GlobalTheory.CartanZero
variable {T : Type 1} [Category.{0} T]

def Good (C : T ⥤ AbCx) (j : ℤ) : Prop :=
  ∀ i, i + 1 = j → ∀ (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X),
    (∀ n, WExact (term C n) a) → ∀ k : ℕ,
      ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ cyc C i j)).ExactAt (k + 1)

theorem good_of_le (C : T ⥤ AbCx) (b : ℤ) (hb : ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n))
    (j : ℤ) (hj : j ≤ b) : Good C j := by
  intro i hi U X a _ k
  have hs : ∀ V, Subsingleton ((cyc C i j).obj V) := fun V => by
    have : Subsingleton ((C.obj V).X i) := AddCommGrpCat.subsingleton_of_isZero (hb i (by omega) V)
    change Subsingleton (((C.obj V).d i j).hom.ker)
    infer_instance
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x _
  exact ⟨0, (hs _).elim _ _⟩

theorem step (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx)
    (hR : Refines Cov (fun U X a => ∀ n, WExact (term C n) a)) (hL : LocExact Cov C)
    (j : ℤ) (hG : Good C j) (U : T) (z : (C.obj U).X j) (hz : (C.obj U).d j (j + 1) z = 0) :
    ∃ y : (C.obj U).X (j - 1), (C.obj U).d (j - 1) j y = z := by
  obtain ⟨V, g, hg, y, hy⟩ := hL j U z hz
  obtain ⟨X, a, h, hgh, hW⟩ := hR U V g hg
  have hZ := hG (j - 1) (by omega) U X a hW 0
  refine GlobalTheory.CartanStep.cartan_step T U X a (cyc C (j - 1) j) (term C (j - 1)) (term C j) (incl C (j - 1) j)
    (dN C (j - 1) j) (fun V => Subtype.val_injective) (fun V y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, ?_⟩) (hW _) (hW _) hZ z
    ((C.map h).f (j - 1) y) ?_
  · rintro ⟨w, rfl⟩
    exact w.2
  · change (C.obj _).d (j - 1) j ((C.map h).f (j - 1) y) = (C.map (a.app _)).f j z
    have e := ConcreteCategory.congr_hom ((C.map h).comm (j - 1) j) y
    simp only [ConcreteCategory.comp_apply] at e
    rw [e, hy, ← hgh, Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

end GlobalTheory.CartanZero

namespace GlobalTheory.CartanZero

theorem good_succ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx)
    (hR : Refines Cov (fun U X a => ∀ n, WExact (term C n) a)) (hL : LocExact Cov C)
    (j : ℤ) (hG : Good C j) : Good C (j + 1) := by
  intro i hi U X a hW
  obtain rfl : i = j := by omega
  refine cosimplicial_ses_exactAt_succ (X ⋙ cyc C (i - 1) i) (X ⋙ term C (i - 1)) (X ⋙ cyc C i (i + 1))
    (Functor.whiskerLeft X (incl C (i - 1) i)) (Functor.whiskerLeft X (pN C (i - 1) i (i + 1)))
    (fun k => Subtype.val_injective) (fun k y => ⟨fun h => ⟨⟨y, congrArg Subtype.val h⟩, rfl⟩, ?_⟩) ?_
    (hG (i - 1) (by omega) U X a hW) (hW (i - 1)).2.2
  · rintro ⟨w, rfl⟩
    exact Subtype.ext w.2
  · intro k c
    obtain ⟨y, hy⟩ := step T Cov C hR hL i hG (X.obj k) c.1 c.2
    exact ⟨y, Subtype.ext hy⟩

theorem cartan_zero : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n)) → Refines Cov (fun U X a => ∀ n, WExact (term C n) a) → LocExact Cov C → ∀ (U : T) (n : ℤ) (z : (C.obj U).X n), (C.obj U).d n (n + 1) z = 0 → ∃ y : (C.obj U).X (n - 1), (C.obj U).d (n - 1) n y = z := by
  intro T _ Cov C ⟨b, hb⟩ hR hL U n z hz
  have hall : ∀ t : ℕ, Good C (b + t) := by
    intro t
    induction t with
    | zero => simpa using good_of_le C b hb b le_rfl
    | succ t ih =>
      have := good_succ T Cov C hR hL _ ih
      simpa [add_assoc] using this
  have hGn : Good C n := by
    by_cases h : n ≤ b
    · exact good_of_le C b hb n h
    · have e : b + ((n - b).toNat : ℤ) = n := by omega
      have h2 := hall (n - b).toNat
      rw [e] at h2
      exact h2
  exact step T Cov C hR hL n hGn U z hz

end GlobalTheory.CartanZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasis
section
open Filter Topology ValuativeRel

noncomputable section

namespace GlobalTheory.LinSchurLatt

theorem eq_one_of_pow_near (z : ℂ) (h : ∀ m : ℕ, ‖z ^ m - 1‖ ≤ 1 / 2) : z = 1 := by
  have hre : ∀ m : ℕ, 1 / 2 ≤ (z ^ m).re := by
    intro m
    have h1 := (Complex.abs_re_le_norm (z ^ m - 1)).trans (h m)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_le.1 h1).1]
  have hS : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ m ∈ Finset.range N, z ^ m‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ m ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun m _ => hre m
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have e := geom_sum_mul z N
  have h2 : ‖z - 1‖ * ((N : ℝ) / 2) ≤ 1 / 2 := by
    calc ‖z - 1‖ * ((N : ℝ) / 2) ≤ ‖z - 1‖ * ‖∑ m ∈ Finset.range N, z ^ m‖ :=
          mul_le_mul_of_nonneg_left (hS N) hpos.le
      _ = ‖z ^ N - 1‖ := by rw [← e, norm_mul, mul_comm]
      _ ≤ 1 / 2 := h N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_natCast_le_one (m : ℕ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)

theorem ker_int_mem_nhds (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) :
    {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} ∈ 𝓝 (0 : k) := by
  have hO : IsCompact {x : k | valuation k x ≤ 1} := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hU : {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} ∈ 𝓝 (0 : k) := by
    have h1 : Metric.closedBall (ψ0 0) (1 / 2) ∈ 𝓝 (ψ0 0) := Metric.closedBall_mem_nhds _ (by norm_num)
    filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with u hu
    simpa [Metric.mem_closedBall, dist_eq_norm, AddChar.map_zero_eq_one] using hu
  have hev : ∀ᶠ w in 𝓝 (0 : k), ∀ a ∈ {x : k | valuation k x ≤ 1}, a * w ∈ {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have hcm : Continuous fun z : k × k => z.2 * z.1 := continuous_snd.mul continuous_fst
    have h0 : (fun z : k × k => z.2 * z.1) (0, a) = 0 := by simp
    exact hcm.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [hev] with w hw o ho
  apply eq_one_of_pow_near
  intro m
  have hmo : valuation k ((m : k) * o) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' (valuation_natCast_le_one m) ho
  have h1 := hw _ hmo
  have h2 : (m : k) * o * w = m • (o * w) := by rw [nsmul_eq_mul, mul_assoc]
  rwa [h2, AddChar.map_nsmul_eq_pow] at h1

theorem ker_int_lt {ψ0 : AddChar k ℂ} {t : k} (ht : ψ0 t ≠ 1) {u : k}
    (hu : ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1) : valuation k u < valuation k t := by
  by_contra h
  push_neg at h
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply ht
    have : t = 0 := by simpa using h
    rw [this, AddChar.map_zero_eq_one]
  have hvu : valuation k u ≠ 0 := by simpa using hu0
  apply ht
  have hle : valuation k (t / u) ≤ 1 := by
    rw [map_div₀, div_eq_mul_inv]
    calc valuation k t * (valuation k u)⁻¹ ≤ valuation k u * (valuation k u)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hvu
  have := hu (t / u) hle
  rwa [div_mul_cancel₀ _ hu0] at this

theorem nhdsNE_neBot' : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_ball_mat (n d : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} := by
  have : {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} =
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem exists_smul_int_mem' (n d : ℕ) (W : Set (Matrix (Fin n) (Fin d) k)) (hW : W ∈ 𝓝 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) k, (∀ i j, valuation k (x i j) ≤ 1) → c • x ∈ W := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ 1}, c • x ∈ W := by
    refine (isCompact_ball_mat n d 1).eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have h0 : (fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2) (0, y) = 0 := by simp
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  haveI := nhdsNE_neBot' (k := k)
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and
    (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

end GlobalTheory.LinSchurLatt

namespace GlobalTheory.LinSchurLatt

theorem latt_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  intro k _ _ _ _ n d ψ0 hc hne
  obtain ⟨t, ht⟩ : ∃ t, ψ0 t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ0)
  have hvt : valuation k t ≠ 0 := by simpa using ht0
  have hK := ker_int_mem_nhds ψ0 hc
  refine ⟨fun s hs => ⟨?_, ?_⟩, fun W hW => ?_⟩
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hev : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ i j,
        s * Y i j ∈ {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} := by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      have hcont : Continuous fun Y : Matrix (Fin n) (Fin d) k => s * Y i j :=
        continuous_const.mul (continuous_id.matrix_elem i j)
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    filter_upwards [hev] with Y hY
    exact GlobalTheory.LinSchur.mem_latt.2 fun i j o ho => hY i j o ho
  · have hsub : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆
        {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ valuation k t * (valuation k s)⁻¹} := by
      intro Y hY i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have hvs : valuation k s ≠ 0 := by simpa using hs
      rw [map_mul] at h1
      calc valuation k (Y i j) = valuation k s * valuation k (Y i j) * (valuation k s)⁻¹ := by
            rw [mul_comm (valuation k s), mul_assoc, mul_inv_cancel₀ hvs, mul_one]
        _ ≤ valuation k t * (valuation k s)⁻¹ := by gcongr
    have hcl : IsClosed (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) := by
      have e : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) =
          ⋂ i, ⋂ j, ⋂ o : {o : k // valuation k o ≤ 1}, {Y | ψ0 (o.1 * (s * Y i j)) = 1} := by
        ext Y
        simp only [SetLike.mem_coe, GlobalTheory.LinSchur.mem_latt, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
      rw [e]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun o =>
        isClosed_eq (hc.comp (continuous_const.mul (continuous_const.mul (continuous_id.matrix_elem i j))))
          continuous_const
    exact (isCompact_ball_mat n d _).of_isClosed_subset hcl hsub
  · obtain ⟨c, hc0, hcW⟩ := exists_smul_int_mem' n d W hW
    refine ⟨t / c, div_ne_zero ht0 hc0, fun Y hY => ?_⟩
    have hx : ∀ i j, valuation k ((c⁻¹ • Y) i j) ≤ 1 := by
      intro i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have e : (c⁻¹ • Y) i j = (t / c * Y i j) * t⁻¹ := by
        rw [Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [e, map_mul, map_inv₀]
      calc valuation k (t / c * Y i j) * (valuation k t)⁻¹ ≤ valuation k t * (valuation k t)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvt
    have := hcW _ hx
    rwa [smul_smul, mul_inv_cancel₀ hc0, one_smul] at this

end GlobalTheory.LinSchurLatt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteOverBase
section
open IsLocalRing Polynomial
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_finite_over_base : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  classical
  let GF := GlobalTheory.LocAcyc.GenFib A R
  let S := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let K' := FractionRing R
  have hS : ∀ y : S, IsUnit (algebraMap R K' y) := by
    rintro ⟨y, a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro h0
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    have : a = 0 := hinj (by simpa using h0)
    exact nonZeroDivisors.ne_zero ha this
  let g : GF →+* K' := IsLocalization.lift (M := S) hS
  let : Algebra GF K' := g.toAlgebra
  have : IsScalarTower R GF K' :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := S) hS r).symm)
  have hg : Function.Injective (algebraMap GF K') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    change g (IsLocalization.mk' GF r s) = 0 at hx
    show IsLocalization.mk' GF r s = 0
    rw [IsLocalization.lift_mk', mul_eq_zero] at hx
    rcases hx with hx | hx
    · rw [IsFractionRing.to_map_eq_zero_iff] at hx
      rw [hx, IsLocalization.mk'_zero]
    · exact absurd hx (Units.ne_zero _)
  let L' := K' ⊗[GF] D
  let ι : D →ₐ[GF] L' := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := by
    have h1 : Function.Injective ((Algebra.linearMap GF K').rTensor D) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hg
    intro x y hxy
    apply (TensorProduct.lid GF D).symm.injective
    apply h1
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have key : (ι : D →+* L').comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = algebraMap R L' := by
    ext r
    show ι (algebraMap GF D (algebraMap R GF r)) = algebraMap R L' r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply GF K' L', IsScalarTower.algebraMap_apply R K' L',
      ← IsScalarTower.algebraMap_apply R GF K']
  let : Algebra R (GlobalTheory.KeyOriginNoeth.closure A R D) :=
    GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let Φ : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] integralClosure R L' :=
    { toFun := fun c => ⟨ι c.1, by
        have hc : (GlobalTheory.KeyOriginNoeth.baseHom A R D).IsIntegralElem c.1 := c.2
        obtain ⟨p, hp, he⟩ := hc
        refine ⟨p, hp, ?_⟩
        have h2 := Polynomial.hom_eval₂ p (GlobalTheory.KeyOriginNoeth.baseHom A R D) (ι : D →+* L') c.1
        rw [he, map_zero] at h2
        rw [← key]
        exact h2.symm⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show ι (x.1 + y.1) = ι x.1 + ι y.1
        exact map_add ι _ _
      map_smul' := fun r c => by
        apply Subtype.ext
        show ι (GlobalTheory.KeyOriginNoeth.baseHom A R D r * c.1) = r • ι c.1
        rw [map_mul, Algebra.smul_def]
        congr 1
        exact RingHom.congr_fun key r }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  have := GlobalTheory.ClosureFinite.integralClosure_finite_of_etale R K' L'
  have := isNoetherian_of_injective Φ hΦ
  exact Module.IsNoetherian.finite R _
end

