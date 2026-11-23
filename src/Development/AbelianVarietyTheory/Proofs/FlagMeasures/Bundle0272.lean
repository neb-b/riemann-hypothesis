module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
section
open MeasureTheory Formalism.MainNotions.S NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongIndex

theorem measure_le_card_mul {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [Finite Q] (K H : Set G) (q : K → Q)
    (hq : ∀ x y : K, q x = q y → (y : G)⁻¹ * x ∈ H) : μ K ≤ (Nat.card Q : ENNReal) * μ H := by
  classical
  haveI := Fintype.ofFinite Q
  have h1 : K ⊆ ⋃ c : Q, Subtype.val '' (q ⁻¹' {c}) := fun x hx =>
    Set.mem_iUnion.2 ⟨q ⟨x, hx⟩, ⟨x, hx⟩, rfl, rfl⟩
  have h2 : ∀ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) ≤ μ H := by
    intro c
    by_cases h : ∃ y, q y = c
    · obtain ⟨y, rfl⟩ := h
      rw [← measure_preimage_mul μ (y : G)⁻¹ H]
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hq x y hx
    · have : q ⁻¹' {c} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => h ⟨y, hy⟩
      simp [this]
  calc μ K ≤ ∑ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) :=
        (measure_mono h1).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _c : Q, μ H := Finset.sum_le_sum fun c _ => h2 c
    _ = _ := by simp [Nat.card_eq_fintype_card]

section Lift

variable {O A L n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
  [AddCommGroup L] [Module O L] (S : Subring A) (ι : L →ₗ[O] (n → A)) (a : A)

theorem exists_approx (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    {y : n → A} (hy : y ∈ Submodule.span S (Set.range ι)) :
    ∃ l : L, ∃ z ∈ Submodule.span S (Set.range ι), y = ι l + a • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨l', z', hz', rfl⟩ := hy
    exact ⟨l + l', z + z', add_mem hz hz', by rw [map_add (f := _), smul_add]; abel⟩
  | smul s x _ hx =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨o, w, hw, e⟩ := hS s s.2
    refine ⟨o • l, (⟨w, hw⟩ : S) • ι l + s • z,
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [map_smul, ← algebraMap_smul A o]
    simp only [Subring.smul_def, smul_add, smul_smul]
    rw [e, add_smul, mul_comm a (_ + _), add_assoc]

theorem exists_end [Module.Projective O L] (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    (x : Matrix n n A) (hx : ∀ y ∈ Submodule.span S (Set.range ι), x *ᵥ y ∈ Submodule.span S (Set.range ι)) :
    ∃ φ : L →ₗ[O] L, ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), x *ᵥ ι l = ι (φ l) + a • z := by
  let N : Submodule O (n → A) :=
    { carrier := {w | ∃ z ∈ Submodule.span S (Set.range ι), w = a • z}
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
        exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro o _ ⟨z, hz, rfl⟩
        refine ⟨(⟨_, hO o⟩ : S) • z, Submodule.smul_mem _ _ hz, ?_⟩
        rw [Subring.smul_def, smul_comm a, algebraMap_smul] }
  let f : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ ι
  let h : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ (Matrix.mulVecLin x).restrictScalars O ∘ₗ ι
  have hh : ∀ l, h l ∈ LinearMap.range f := by
    intro l
    obtain ⟨l', z, hz, e⟩ := exists_approx S ι a hO hS ha (hx _ (Submodule.subset_span ⟨l, rfl⟩))
    refine ⟨l', ((Submodule.Quotient.eq N).2 ⟨z, hz, ?_⟩).symm⟩
    exact sub_eq_of_eq_add' e
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f.rangeRestrict (h.codRestrict _ hh)
    f.surjective_rangeRestrict
  refine ⟨φ, fun l => ?_⟩
  have e : f (φ l) = h l := congrArg Subtype.val (LinearMap.congr_fun hφ l)
  obtain ⟨z, hz, e'⟩ := (Submodule.Quotient.eq N).1 e.symm
  exact ⟨z, hz, eq_add_of_sub_eq' e'⟩

theorem congr_of_end (g : ℕ) (x y : GL n A)
    (hx : x ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι)))
    (hy : y ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι))) (φ ψ θ : L →ₗ[O] L)
    (hφ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (x : Matrix n n A) *ᵥ ι l = ι (φ l) + (g : A) • z)
    (hψ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (y : Matrix n n A) *ᵥ ι l = ι (ψ l) + (g : A) • z)
    (hθ : φ = ψ + g • θ) :
    y⁻¹ * x ∈ GlobalTheory.CongTop.cong (Submodule.span S (Set.range ι)) (g : A) := by
  refine ⟨mul_mem (inv_mem hy) hx, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, rfl⟩ := hv
    obtain ⟨z, hz, e⟩ := hφ l
    obtain ⟨z', hz', e'⟩ := hψ l
    refine ⟨((y⁻¹ : GL n A) : Matrix n n A) *ᵥ (ι (θ l) + z - z'),
      (inv_mem hy _).1 (sub_mem (add_mem (Submodule.subset_span ⟨_, rfl⟩) hz) hz'), ?_⟩
    have e2 : (x : Matrix n n A) *ᵥ ι l - (y : Matrix n n A) *ᵥ ι l = (g : A) • (ι (θ l) + z - z') := by
      rw [e, e', hθ, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_nsmul,
        ← Nat.cast_smul_eq_nsmul A, smul_sub, smul_add]
      abel
    rw [← Matrix.mulVec_smul, ← e2, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Units.inv_mul, Units.val_mul, Matrix.sub_mulVec]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨z, hz, e⟩ := hv
    obtain ⟨z', hz', e'⟩ := hw
    exact ⟨z + z', add_mem hz hz', by rw [Matrix.mulVec_add, e, e', smul_add]⟩
  | smul s v _ hv =>
    obtain ⟨z, hz, e⟩ := hv
    refine ⟨s • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, Matrix.mulVec_smul, e, smul_comm]

end Lift

section Rank

variable {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_inj (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ m ≤ n, ∃ e : (L →ₗ[𝓞 E] L) →ₗ[ℤ] (Fin m → Fin n → E), Function.Injective e := by
  obtain ⟨b, hbL, hb, hli⟩ := exists_linearIndependent E (L : Set (Fin n → E))
  haveI : Finite b := hli.finite
  haveI := Fintype.ofFinite b
  have hc : Fintype.card b ≤ n := by simpa using hli.fintype_card_le_finrank
  let u := (Fintype.equivFin b).symm
  let e : (L →ₗ[𝓞 E] L) →+ (Fin (Fintype.card b) → Fin n → E) :=
    { toFun := fun φ i => (φ ⟨u i, hbL (u i).2⟩ : L)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  refine ⟨_, hc, e.toIntLinearMap, (injective_iff_map_eq_zero e).2 fun φ hφ => ?_⟩
  ext1 l
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E b (l : Fin n → E)
    (by rw [hb, hL]; trivial)
  have hle : Submodule.span (𝓞 E) b ≤ (LinearMap.ker φ).map L.subtype := by
    refine Submodule.span_le.2 fun w hw => ⟨⟨w, hbL hw⟩, ?_, rfl⟩
    have := congrFun hφ (u.symm ⟨w, hw⟩)
    simpa [e] using this
  obtain ⟨l', hl', e'⟩ := hle ht
  have e2 : l' = (t : 𝓞 E) • l := Subtype.ext e'
  rw [e2, SetLike.mem_coe, LinearMap.mem_ker, map_smul, smul_eq_zero] at hl'
  exact hl'.resolve_left (nonZeroDivisors.ne_zero t.2)

theorem card_end_quot (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) :
    ∃ r ≤ n ^ 2 * Module.finrank ℚ E,
      (nsmulAddMonoidHom (α := L →ₗ[𝓞 E] L) g).range.index = g ^ r := by
  obtain ⟨m, hm, e, he⟩ := exists_inj L hL
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  haveI : IsNoetherian (𝓞 E) L := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (𝓞 E) (L →ₗ[𝓞 E] L) := isNoetherian_linearMap _ _ _
  haveI : Module.Finite (𝓞 E) (L →ₗ[𝓞 E] L) := Module.IsNoetherian.finite _ _
  haveI : Module.Finite ℤ (L →ₗ[𝓞 E] L) := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ (L →ₗ[𝓞 E] L) := he.moduleIsTorsionFree e e.map_smul
  refine ⟨_, ?_, AddSubgroup.index_range_nsmul _ g⟩
  have h1 := e.rank_le_of_injective he
  rw [← IsFractionRing.rank_right_eq ℤ ℚ (Fin m → Fin n → E), ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank, Nat.cast_le] at h1
  refine h1.trans ?_
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, sq]
  gcongr

end Rank

theorem measure_Kset_le : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] (g : ℕ), 1 ≤ g → μf I.Kset ≤ (g : ENNReal) ^ (2 * (I.n ^ 2 * I.f)) * μf (I.Kg g) ∧ 0 < μf (I.Kg g) ∧ μf I.Kset < ⊤ := by
  intro I μf _ g hg
  obtain ⟨-, -, hsc, hc, -, -, h⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨ho, ⟨H, hH⟩, -⟩ := h g hg
  refine ⟨?_, ho.measure_pos μf ⟨1, hH ▸ H.one_mem⟩, hc.measure_lt_top⟩
  haveI : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  haveI : Module.FinitePresentation (𝓞 I.E) I.L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 I.E) I.L := Module.Flat.projective_of_finitePresentation
  let ι : I.L →ₗ[𝓞 I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    { toFun := fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => rfl }
  have hL : I.Lf = Submodule.span (IntAf I.F I.E) (Set.range ι) := rfl
  have hO : ∀ o : 𝓞 I.E, algebraMap _ (I.E ⊗[I.F] Af I.F) o ∈ IntAf I.F I.E := fun o =>
    Formalism.UG.P.levelaf_tmul_mem o (one_mem _)
  have hS : ∀ s ∈ IntAf I.F I.E, ∃ o : 𝓞 I.E, ∃ w ∈ IntAf I.F I.E,
      s = algebraMap _ (I.E ⊗[I.F] Af I.F) o + (g : I.E ⊗[I.F] Af I.F) * w := by
    intro s hs
    obtain ⟨x, hx, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := I.F) (E := I.E) Formalism.UG.P.csGlob_intAdApprox (g : 𝓞 I.F)
      (Nat.cast_ne_zero.2 (by omega)) hs
    refine ⟨⟨x, hx⟩, w, hw, ?_⟩
    rw [e, ← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]
    rfl
  have key := fun x : I.Kset => exists_end (IntAf I.F I.E) ι (g : I.E ⊗[I.F] Af I.F) hO hS
    (natCast_mem _ g) (I.fmat x) fun y hy => (x.2 y).1 hy
  choose φ hφ using key
  obtain ⟨r, hr, hi⟩ := card_end_quot I.L I.L_span I.L_fg g
  set N := (nsmulAddMonoidHom (α := I.L →ₗ[𝓞 I.E] I.L) g).range
  have hi' : Nat.card ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) = g ^ r := hi
  haveI : Finite ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hi']; positivity)
  have h1 := measure_le_card_mul μf I.Kset (I.Kg g) (fun x => (QuotientAddGroup.mk (φ x) : _ ⧸ N))
    fun x y hxy => by
      obtain ⟨θ, hθ⟩ := QuotientAddGroup.eq.1 hxy.symm
      exact congr_of_end (IntAf I.F I.E) ι g _ _ x.2 y.2 (φ x) (φ y) θ (hφ x) (hφ y)
        (by rw [show g • θ = -φ y + φ x from hθ]; abel)
  refine h1.trans ?_
  rw [hi', Nat.cast_pow]
  have h2 : Module.finrank ℚ I.E = I.f * 2 := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]; rfl
  gcongr
  · exact_mod_cast hg
  · rw [h2] at hr; linarith

end GlobalTheory.CongIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToGivesIntegralMatrices
section
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedFrames

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem exists_coef_of_mem_span_image {V : Type*} [AddCommGroup V] [Module E V] (e : Fin r → V)
    (s : Set (Fin r)) {x : V} (hx : x ∈ Submodule.span E (e '' s)) :
    ∃ l : Fin r → E, (∀ k, k ∉ s → l k = 0) ∧ x = ∑ k, l k • e k := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h; exact hk (hl (Finsupp.mem_support_iff.mpr h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]; intro i; simp

theorem z_mem_orth (F : FlagG S r T) : F.z ∈ orth S (Submodule.span E (Set.range F.e)) := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.z_orth a
  | zero => simp
  | add a b _ _ ha hb => simp [map_add (f := _), ha, hb]
  | smul c a _ ha => simp [ha]

theorem exists_upUni (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V)
    (h1 : ∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j)
    (h2 : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = 1) ∧
      ∀ b, n (frame F b) = ∑ a, W a b • frame F a := by
  have key : ∀ b : Fin (r + 1), ∃ l : Fin r → E, (∀ k, b ≤ Fin.castSucc k → l k = 0) ∧
      n (frame F b) = frame F b + ∑ k, l k • F.fl.e k := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
      have hm := h2 _ (z_mem_orth F.fl)
      have hm' : n F.fl.z - F.fl.z ∈ Submodule.span E (F.fl.e '' Set.univ) := by
        rw [Set.image_univ]; exact hm
      obtain ⟨l, -, hl⟩ := exists_coef_of_mem_span_image F.fl.e Set.univ hm'
      refine ⟨l, fun k hk => absurd hk (not_le.mpr (Fin.castSucc_lt_last k)), ?_⟩
      rw [hz, ← hl]; abel
    | cast i =>
      have hf : frame F (Fin.castSucc i) = F.fl.e i := by simp [frame, FlagG.fvec]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span (Set.mem_image_of_mem _ (show i ∈ {k : Fin r | k.1 < i.1 + 1} from Nat.lt_succ_self _))
      have hm : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1}) := by
        have := h1 i.val _ hmem
        rw [hf] at *
        exact this
      obtain ⟨l, hl0, hl⟩ := exists_coef_of_mem_span_image F.fl.e _ hm
      refine ⟨l, fun k hk => hl0 k ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, not_lt]; exact Fin.castSucc_le_castSucc_iff.mp hk
      · rw [hf, ← hl]; abel
  choose l hl0 hl using key
  refine ⟨Matrix.of fun a b => Fin.snoc (α := fun _ => E) (l b) 0 a + if a = b then 1 else 0, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [Matrix.of_apply, if_neg (ne_of_gt hab), add_zero]
    induction a using Fin.lastCases with
    | last => simp
    | cast k => simp only [Fin.snoc_castSucc]; exact hl0 b k hab.le
  · intro a
    simp only [Matrix.of_apply, if_pos rfl]
    induction a using Fin.lastCases with
    | last => simp
    | cast k => simp only [Fin.snoc_castSucc]; rw [hl0 _ k le_rfl]; simp
  · intro b
    rw [hl b]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp [frame, FlagG.fvec, add_comm]

theorem upUni_mul {N : ℕ} {U W : Matrix (Fin N) (Fin N) E} (hU0 : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) (hW0 : ∀ a b, b < a → W a b = 0) (hW1 : ∀ a, W a a = 1) :
    (∀ a b, b < a → (U * W) a b = 0) ∧ (∀ a, (U * W) a a = 1) := by
  first
  | exact @_root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
  | exact _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
  | (apply _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul ..)

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (b : Fin (r + 1)) :
    frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast k => simp [frame, FlagG.fvec, mapFlag]

end Gen

end GlobalTheory.MovedFrames

namespace GlobalTheory.MovedFrames

theorem map_sum_frame {E V : Type*} [Field E] [AddCommGroup V] [Module E V] {N : ℕ} (ρ : V ≃ₗ[E] V)
    (U W : Matrix (Fin N) (Fin N) E) (f g : Fin N → V) (hF : ∀ a, ρ (f a) = ∑ c, U c a • g c) (b : Fin N) :
    ρ (∑ a, W a b • f a) = ∑ c, (U * W) c b • g c := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, hF, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

end GlobalTheory.MovedFrames

namespace GlobalTheory.MovedFrames

theorem moved_frames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → ∃ B B' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧ (∀ a b, b < a → B' a b = 0) ∧ (∀ a, B' a a = 1) ∧ ∀ b, ρ (n (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • frame F00 a ∧ ρ (n (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • frame F'0 a := by
  intro D X Y u u' F00 F'0 t₀ ρ U U' hM n m hn hm
  obtain ⟨_, hU, hU', hF, hF'⟩ := hM
  obtain ⟨W, hW0, hW1, hWe⟩ := exists_upUni _ n hn.2.1 hn.2.2
  obtain ⟨W', hW'0, hW'1, hW'e⟩ := exists_upUni _ m hm.2.1 hm.2.2
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem (inv_mem hn.1) hlin) hm.1
  obtain ⟨hB0, hB1⟩ := upUni_mul (fun a b h => (hU a b).1 h) (fun a => (hU a a).2 rfl) hW0 hW1
  obtain ⟨hB'0, hB'1⟩ := upUni_mul (fun a b h => (hU' a b).1 h) (fun a => (hU' a a).2 rfl) hW'0 hW'1
  refine ⟨U * W, U' * W', hB0, hB1, hB'0, hB'1, fun b => ⟨?_, ?_⟩⟩
  · rw [hWe]
    exact map_sum_frame ρ U W _ _ hF b
  · have ht : ∀ a, t₀.lin (frame (lf D (X.Fu u')) a) = frame t₀.frame a := fun a => by
      rw [← frame_mapLF _ hlin]; rfl
    have hx : ∀ x, n ((n⁻¹ * t₀.lin * m) x) = t₀.lin (m x) := fun x => by
      rw [← LinearEquiv.mul_apply, show n * (n⁻¹ * t₀.lin * m) = t₀.lin * m by group,
        LinearEquiv.mul_apply]
    have hF2 : ∀ a, (t₀.lin.trans ρ) (frame (lf D (X.Fu u')) a) = ∑ c, U' c a • frame F'0 c := by
      intro a
      rw [LinearEquiv.trans_apply, ht, hF']
    rw [frame_mapLF _ hγ, hx, hW'e]
    have := map_sum_frame (t₀.lin.trans ρ) U' W' _ _ hF2 b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, LinearEquiv.trans_apply, map_sum]

end GlobalTheory.MovedFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimpleRootCoefEqSuperdiagonalSumFrames
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocCoef

theorem rationalDualPairing_eq_scaledLocalPairing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r k : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : Frames (A.L p) r k) (Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E)
    (c : ((A.loc p).Fp)ˣ) (hHm : S.Hm = Hm.map (A.loc p).ιE)
    (fv : Fin (r + 1) → Fin (k + 2 * r + 1) → E) (ev : Fin r → Fin (k + 2 * r + 1) → E)
    (Sf : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (Se : Fin r → Fin (k + 2 * r + 1) → (A.loc p).Ep)
    (hfe : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • Sf a = A.bc p (fv a))
    (hee : ∀ a : Fin r, Se a = algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (ev a))
    (hd : ∀ a j, hf (A.L p) S.Hm (Sf a) (Se j) = if a = j.castSucc then 1 else 0)
    (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, fv b i * Hm i j * sig (ev a j) = if b = a.castSucc then 1 else 0 := by
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  set α : ℕ → (A.loc p).Ep := fun n => algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - n)) with hα
  have hu : ∀ n, IsUnit (α n) := fun n => ((c.isUnit.pow _)).map _
  have key := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 Hm (fv b) (ev a)
  have h1 : hf (A.L p) S.Hm (A.bc p (fv b)) (Se a) = α b * (if b = a.castSucc then 1 else 0) := by
    rw [← hfe b, ← hd b a]
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : hf (A.L p) S.Hm (A.bc p (fv b)) (Se a) = (A.loc p).ιE (∑ i, ∑ j, fv b i * Hm i j * sig (ev a j)) * α a := by
    rw [hee a, ← key, hHm]
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.sum_mul, hα]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1] at h2
  split_ifs at h2 ⊢ with hb
  · subst hb
    have ha : ((a.castSucc : Fin (r + 1)) : ℕ) = (a : ℕ) := Fin.coe_castSucc a
    rw [ha, mul_one] at h2
    have h3 : (A.loc p).ιE (∑ i, ∑ j, fv a.castSucc i * Hm i j * sig (ev a j)) = (A.loc p).ιE 1 := by
      rw [map_one]
      exact (hu (a : ℕ)).mul_right_cancel (by rw [one_mul]; exact h2.symm)
    exact (A.loc p).ιE.injective h3
  · rw [mul_zero] at h2
    have h3 := ((hu (a : ℕ)).mul_left_eq_zero).mp h2.symm
    exact (A.loc p).ιE.injective (by rw [h3, map_zero])

end GlobalTheory.SlocCoef

namespace GlobalTheory.SlocCoef

theorem pair_f_es {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, G.f b i * G.Hm i j * sig (G.es a j) = if b = a.castSucc then 1 else 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  exact rationalDualPairing_eq_scaledLocalPairing A p (G.S p) G.Hm (G.c p) (G.Hm_eq p) G.f G.es (G.S p).f (G.S p).es
    (G.f_eq p) (G.es_eq p) (G.S p).dual b a

theorem pair_f'_es' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.es' a j) = if b = a.castSucc then 1 else 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  exact rationalDualPairing_eq_scaledLocalPairing A p (G.S p) G.Hm (G.c p) (G.Hm_eq p) G.f' G.es' (G.S p).f' (G.S p).es'
    (G.f'_eq p) (G.es'_eq p) (G.S p).dual' b a

theorem coef_sum {E : Type} [Field E] [NumberField E] (sig : E → E) {r n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (fv : Fin (r + 1) → Fin n → E) (ev : Fin r → Fin n → E)
    (hd : ∀ b a, ∑ i, ∑ j, fv b i * Hm i j * sig (ev a j) = if b = a.castSucc then 1 else 0)
    (N : (Fin n → E) ≃ₗ[E] (Fin n → E)) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : ∀ b, N (fv b) = ∑ a, B a b • fv a) :
    (∑ a : Fin r, ∑ i, ∑ j, N (fv a.succ) i * Hm i j * sig (ev a j)) = Formalism.L2.SG.PairVal.sgUp B := by
  have h1 : ∀ a : Fin r, ∑ i, ∑ j, N (fv a.succ) i * Hm i j * sig (ev a j) = B a.castSucc a.succ := by
    intro a
    rw [hN]
    have e : ∀ i j, (∑ c, B c a.succ • fv c) i * Hm i j * sig (ev a j) =
        ∑ c, B c a.succ * (fv c i * Hm i j * sig (ev a j)) := by
      intro i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    simp_rw [e]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hd]
    simp
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero,
    add_lt_add_iff_right, Fin.is_lt, dif_pos]
  refine Finset.sum_congr rfl fun a _ => ?_
  rfl

end GlobalTheory.SlocCoef

theorem GlobalTheory.SlocCoef.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (N : G.GLV), ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f a.succ) i * G.Hm i j * sig (G.es a j)) = Formalism.L2.SG.PairVal.sgUp B) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) = Formalism.L2.SG.PairVal.sgUp B) := by
  intro F E _ _ _ _ _ sig A r k G B N
  exact ⟨GlobalTheory.SlocCoef.coef_sum sig G.Hm G.f G.es (GlobalTheory.SlocCoef.pair_f_es G) N B,
    GlobalTheory.SlocCoef.coef_sum sig G.Hm G.f' G.es' (GlobalTheory.SlocCoef.pair_f'_es' G) N B⟩
end

