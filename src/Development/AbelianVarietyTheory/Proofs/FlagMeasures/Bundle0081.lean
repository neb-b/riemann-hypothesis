module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnesses
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevels
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem transfer {V : Type} [AddCommGroup V] [Module E V] {m : ℕ} {g g' h h' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) {y : V} {al al' : Fin m → E}
    (e1 : y = ∑ i, al i • g i + ∑ i, al' i • g' i) (e2 : y = ∑ i, al i • h i + ∑ i, al' i • h' i)
    (P : (Fin m → E) → (Fin m → E) → Prop)
    (H : ∃ be be' : Fin m → E, y = ∑ i, be i • g i + ∑ i, be' i • g' i ∧ P be be') :
    ∃ be be' : Fin m → E, y = ∑ i, be i • h i + ∑ i, be' i • h' i ∧ P be be' := by
  obtain ⟨be, be', e3, hP⟩ := H
  have h0 := Fintype.linearIndependent_iff.1 hli (Sum.elim (al - be) (al' - be')) (by
    have := e1.symm.trans e3
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul,
      Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, this, sub_self])
  have a1 : al = be := funext fun i => sub_eq_zero.1 (h0 (Sum.inl i))
  have a2 : al' = be' := funext fun i => sub_eq_zero.1 (h0 (Sum.inr i))
  subst a1 a2
  exact ⟨_, _, e2, hP⟩

theorem mem_Mof (g g' : Fin (r + 1) → S.V) (y : S.V) :
    y ∈ S.Mof g g' ↔ ∃ al al' : Fin (r + 1) → E, y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i, algebraMap F E S.th * al' i ∈ L.O ∧ al i + al' i ∈ L.O := by
  have ht := WitIndep.th_mul S
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · refine ⟨Pi.single b 1, 0, by simp [Pi.single_apply], fun i => ⟨by simp, ?_⟩⟩
        by_cases h : i = b
        · subst h; simp
        · simp [h]
      · refine ⟨Pi.single b (-algebraMap F E S.th⁻¹), Pi.single b (algebraMap F E S.th⁻¹), ?_,
          fun i => ?_⟩
        · simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
            if_true, smul_sub, neg_smul]
          abel
        · by_cases h : i = b
          · subst h
            simp only [Pi.single_eq_same, neg_add_cancel, mul_comm (algebraMap F E S.th), ht]
            exact ⟨L.O.one_mem, L.O.zero_mem⟩
          · simp [h]
    | zero => exact ⟨0, 0, by simp, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      obtain ⟨b, b', rfl, hb⟩ := hy
      refine ⟨a + b, a' + b', ?_, fun i => ⟨?_, ?_⟩⟩
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
      · simpa [mul_add] using L.O.add_mem (ha i).1 (hb i).1
      · have := L.O.add_mem (ha i).2 (hb i).2
        rw [add_add_add_comm] at this
        exact this
    | smul c x _ hx =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      refine ⟨fun i => c * a i, fun i => c * a' i, ?_, fun i => ⟨?_, ?_⟩⟩
      · rw [Subring.smul_def]
        simp only [smul_add, Finset.smul_sum, smul_smul]
      · have := L.O.mul_mem c.2 (ha i).1
        rw [mul_left_comm] at this
        exact this
      · have := L.O.mul_mem c.2 (ha i).2
        rw [mul_add] at this
        exact this
  · rintro ⟨al, al', rfl, h⟩
    rw [← Finset.sum_add_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : al i • g i + al' i • g' i = (al i + al' i) • g i +
        (algebraMap F E S.th * al' i) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
      rw [smul_smul, mul_right_comm, mul_comm (algebraMap F E S.th), ht, one_mul, add_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ (⟨_, (h i).2⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (Submodule.smul_mem _ (⟨_, (h i).1⟩ : L.O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

theorem exists_coef_map {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {n : S.GLV} (hn : n ∈ S.Nof g)
    {J : ℕ} {y : S.V} (hy : y ∈ S.spanTo g J) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), ¬ (i : ℕ) < J → c i = 0) ∧ y = ∑ i, c i • n (g i) := by
  obtain ⟨c, hc, e⟩ := StdLat.exists_coef g _ (TermBasic.map_mem hg ((S.Nof g).inv_mem hn) J hy)
  refine ⟨c, hc, ?_⟩
  have e2 : n (n⁻¹ y) = y := n.apply_symm_apply y
  rw [← e2, e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]

theorem iso_span {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {J : ℕ} {v : S.V}
    (hv : v ∈ S.spanTo g J) : v ∈ perp L S.Hm (S.spanTo g r) := by
  refine (Submodule.span_le.2 ?_ : S.spanTo g J ≤ _) hv
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
  exact hg _

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem indep {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') :
    LinearIndependent E (Sum.elim (fun b => n (S.f b)) (fun b => n' (S.f' b))) := by
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -⟩ := FrameBasic.main L r k S
  obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
  refine LinearIndependent.sum_type (l1.map' n.toLinearMap (LinearEquiv.ker _))
    (l2.map' n'.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    have := TermBasic.map_mem hg hn (r + 1) (TermBasic.self_mem S S.f b.2)
    rw [TermBasic.spanTo_top] at this
    exact this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    have := TermBasic.map_mem hg' hn' (r + 1) (TermBasic.self_mem S S.f' b.2)
    rw [TermBasic.spanTo_top] at this
    exact this

end

theorem move_same : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.IsTerm d Λ₁ ∧ ∀ y ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)), (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧ S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM Λ₁ hΛ₁
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e0i, e0', e'', emv, hW₁⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hsx, -, -, -, -, -, -, -, -, hxX, hxX'⟩ :=
    _root_.GlobalTheory.HL.MoveFacts.move_facts L r k S j β βJ d Λ hT hF x x' u s hM
  have eΛ : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (emv.trans hΛ₁.symm)
  rw [eΛ] at hW₁
  obtain ⟨-, hW, -, -, -, hli, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, eM, -, eL, -⟩ := WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁
  have hli₁ := indep S hW₁.2.2.1 hW₁.2.2.2.1
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨-, -, hb, -, huΛ, hu, -, -⟩ := hM
  have hH := S.herm.1
  have hyu : ∀ y ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm y u = 0 := fun y hy => by
    rw [← hf_cj L hH, hu y hy, map_zero]
  have hJ : (j : ℕ) + 1 ≤ r := j.2
  have hn := hW.2.2.1
  have hn' := hW.2.2.2.1
  have f1 : ∀ i : Fin (r + 1), (i : ℕ) < j + 1 → (n₀⁻¹ * (S.wit d Λ).1) (S.f i) = S.fr d Λ i := by
    intro i hi
    have hm : S.fr d Λ i ∈ S.spanTo S.f (j + 1) :=
      TermBasic.map_mem hg hn _ (TermBasic.self_mem S S.f hi)
    show n₀⁻¹ (S.fr d Λ i) = _
    rw [e0i, eich, hf_neg_r, hyu _ (Submodule.mem_sup_left hm), iso_span S hg hm x hxX]
    simp
  have f2 : ∀ i : Fin (r + 1), (i : ℕ) < j + 1 →
      (n'' * n₀' * (S.wit d Λ).2) (S.f' i) = S.fr' d Λ i := by
    intro i hi
    have hm : S.fr' d Λ i ∈ S.spanTo S.f' (j + 1) :=
      TermBasic.map_mem hg' hn' _ (TermBasic.self_mem S S.f' hi)
    show n'' (n₀' (S.fr' d Λ i)) = _
    rw [e0', eich, hyu _ (Submodule.mem_sup_right hm), iso_span S hg' hm x' hxX']
    simp only [zero_smul, add_zero, sub_zero]
    exact e'' _ (iso_span S hg' hm)
  refine ⟨⟨(_, _), hW₁⟩, fun y hy => ?_⟩
  have hyu0 := hyu y hy
  obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, hc, ec⟩ := exists_coef_map S hg hn hv
  obtain ⟨c', hc', ec'⟩ := exists_coef_map S hg' hn' hv'
  have e1 : v + v' = ∑ i, c i • S.fr d Λ i + ∑ i, c' i • S.fr' d Λ i := by
    rw [ec, ec']; rfl
  have e2 : v + v' = ∑ i, c i • (n₀⁻¹ * (S.wit d Λ).1) (S.f i) +
      ∑ i, c' i • (n'' * n₀' * (S.wit d Λ).2) (S.f' i) := by
    rw [e1]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · by_cases hi : (i : ℕ) < j + 1
      · rw [f1 i hi]
      · rw [hc i hi, zero_smul, zero_smul]
    · by_cases hi : (i : ℕ) < j + 1
      · rw [f2 i hi]
      · rw [hc' i hi, zero_smul, zero_smul]
  refine ⟨fun hyΛ => ?_, ?_, ?_⟩
  · have hvX : v ∈ S.X := TermBasic.spanTo_mono S S.f hJ hv
    have hvX' : v' ∈ S.X' := TermBasic.spanTo_mono S S.f' hJ hv'
    obtain ⟨a, ha, ea⟩ := hF.1.2.2 x hxX x' hxX' _ (S.X.smul_mem (algebraMap F E S.th) hvX) _
      (S.X'.smul_mem (algebraMap F E S.th) hvX') hb ⟨_, hyΛ, (smul_add _ _ _).symm⟩
    rw [Frames.h, hf_smul_r, AlgEquiv.commutes] at ea
    have ea2 : hf L S.Hm x v' = a := by
      have := congrArg (algebraMap F E S.th⁻¹ * ·) ea
      simpa only [← mul_assoc, WitIndep.th_mul S, one_mul] using this
    have ea3 : hf L S.Hm (v + v') x = L.cj a := by
      rw [hf_add_l, iso_span S hg hv x hxX, zero_add, ← ea2, hf_cj L hH]
    rw [← SetLike.mem_coe, hΛ₁]
    show eich L S.Hm x u s (v + v') ∈ Λ
    rw [eich, hyu0, ea3, zero_smul, add_zero]
    exact Λ.sub_mem hyΛ (Λ.smul_mem (⟨_, UnramOrder.cj_mem L ha⟩ : L.O) (Λ.add_mem huΛ hsx))
  · rw [eM, Frames.M, mem_Mof, mem_Mof]
    exact ⟨transfer hli₁ e2 e1 _, transfer hli e1 e2 _⟩
  · rw [eL, Frames.lev, Frames.lev]
    congr 1
    ext t
    exact ⟨transfer hli₁ e2 e1 _, transfer hli e1 e2 _⟩

end GlobalTheory.HL.MoveSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralAdeleIdealOfIdealPrincipalAndInter
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Formalism.UG Formalism.UG.P Inhab

theorem map_eq_span_of_idem {O S : Type} [CommRing O] [CommRing S] (ψ : O →+* S) (𝔞 : Ideal O) (hfg : 𝔞.FG)
    (m a : O) (hm : m ∈ 𝔞) (ha : Ideal.span {m} * 𝔞 ⊔ Ideal.span {a} = 𝔞) (μ : S)
    (hidem : (μ * ψ m) * (μ * ψ m) = μ * ψ m)
    (hjac : (1 - μ * ψ m) * ψ m ∈ Ideal.jacobson (⊥ : Ideal S)) :
    ∃ t : S, 𝔞.map ψ = Ideal.span {t} := by
  generalize he : μ * ψ m = e at hidem hjac
  have hb : Ideal.span {ψ m} * 𝔞.map ψ ⊔ Ideal.span {ψ a} = 𝔞.map ψ := by
    conv_rhs => rw [← ha]
    rw [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton]
  have haa : a ∈ 𝔞 := by
    rw [← ha]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have ha' : ψ a ∈ 𝔞.map ψ := Ideal.mem_map_of_mem ψ haa
  have he' : e ∈ 𝔞.map ψ := by
    rw [← he]
    exact Ideal.mul_mem_left _ μ (Ideal.mem_map_of_mem ψ hm)
  refine ⟨e + (1 - e) * ψ a, le_antisymm ?_ ?_⟩
  · have h1 : e ∈ Ideal.span {e + (1 - e) * ψ a} :=
      Ideal.mem_span_singleton'.2 ⟨e, by linear_combination (1 - ψ a) * hidem⟩
    have h2 : (1 - e) * ψ a ∈ Ideal.span {e + (1 - e) * ψ a} :=
      Ideal.mem_span_singleton'.2 ⟨1 - e, by linear_combination (ψ a - 1) * hidem⟩
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (hfg.map ψ)
      ((Ideal.span_singleton_le_iff_mem _).2 hjac) ?_
    intro x hx
    rw [← hb] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Submodule.mem_sup.2 ⟨e * (ψ m * w + s * ψ a) + s * ((1 - e) * ψ a), ?_,
      ((1 - e) * ψ m) • w, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw, ?_⟩
    · exact add_mem (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · rw [smul_eq_mul]
      ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact add_mem he' (Ideal.mul_mem_left _ _ ha')

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_intAd (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, Valued.v (f v) ≤ 1) : ∃ x : intAd F, ∀ v, (x : Af F) v = f v := by
  have hmem : ∀ v, f v ∈ v.adicCompletionIntegers F := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hf v
  exact ⟨⟨⟨f, Filter.Eventually.of_forall hmem⟩, hmem⟩, fun _ => rfl⟩

theorem intAd_ext {x y : intAd F} (h : ∀ v, (x : Af F) v = (y : Af F) v) : x = y := by
  apply Subtype.ext
  exact DFunLike.ext _ _ h

theorem isUnit_intAd (x : intAd F) (hx : ∀ v, Valued.v ((x : Af F) v) = 1) : IsUnit x := by
  have hne : ∀ v, (x : Af F) v ≠ 0 := fun v h0 => by simpa [h0] using hx v
  obtain ⟨y, hy⟩ := exists_intAd (fun v => ((x : Af F) v)⁻¹)
    (fun v => by rw [map_inv₀, hx v, inv_one])
  have hxy : x * y = 1 := by
    refine intAd_ext fun v => ?_
    show (x : Af F) v * (y : Af F) v = (1 : Af F) v
    rw [hy v, mul_inv_cancel₀ (hne v)]
    rfl
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem exists_idem_intAd (x : intAd F) : ∃ μ : intAd F, (μ * x) * (μ * x) = μ * x ∧
    (1 - μ * x) * x ∈ Ideal.jacobson (⊥ : Ideal (intAd F)) := by
  classical
  have hx2 : ∀ v, (x : Af F) v ∈ v.adicCompletionIntegers F := x.2
  have hle : ∀ v, Valued.v ((x : Af F) v) ≤ 1 := fun v => by
    have := hx2 v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  obtain ⟨μ, hμ⟩ := exists_intAd
    (fun v => if Valued.v ((x : Af F) v) = 1 then ((x : Af F) v)⁻¹ else 0)
    (fun v => by
      split_ifs with h
      · rw [map_inv₀, h, inv_one]
      · rw [map_zero]
        exact zero_le)
  have hprod : ∀ v, ((μ * x : intAd F) : Af F) v =
      if Valued.v ((x : Af F) v) = 1 then 1 else 0 := by
    intro v
    show (μ : Af F) v * (x : Af F) v = _
    rw [hμ v]
    split_ifs with h
    · refine inv_mul_cancel₀ fun h0 => ?_
      rw [h0, map_zero] at h
      exact zero_ne_one h
    · exact zero_mul _
  refine ⟨μ, intAd_ext fun v => ?_, Ideal.mem_jacobson_bot.2 fun y => isUnit_intAd _ fun v => ?_⟩
  · show ((μ * x : intAd F) : Af F) v * ((μ * x : intAd F) : Af F) v = ((μ * x : intAd F) : Af F) v
    rw [hprod v]
    split_ifs <;> simp
  · have hy2 : ∀ w, (y : Af F) w ∈ w.adicCompletionIntegers F := y.2
    have hyle : Valued.v ((y : Af F) v) ≤ 1 := by
      have := hy2 v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    show Valued.v ((1 - ((μ * x : intAd F) : Af F) v) * (x : Af F) v * (y : Af F) v + 1) = 1
    by_cases h : Valued.v ((x : Af F) v) = 1
    · rw [hprod v, if_pos h, sub_self, zero_mul, zero_mul, zero_add, map_one]
    · rw [hprod v, if_neg h, sub_zero, one_mul, add_comm]
      apply Valuation.map_one_add_of_lt
      rw [map_mul]
      calc Valued.v ((x : Af F) v) * Valued.v ((y : Af F) v) ≤ Valued.v ((x : Af F) v) * 1 :=
            by gcongr
        _ < 1 := by
            rw [mul_one]
            exact lt_of_le_of_ne (hle v) h

noncomputable def intAdIncl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAd F →+* IntAf F E :=
  ((Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F).toRingHom.comp (intAd F).subtype).codRestrict _
    fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)

theorem intAdIncl_isIntegral : (intAdIncl F E).IsIntegral := by
  let _ : Algebra (intAd F) (IntAf F E) := (intAdIncl F E).toAlgebra
  have hpsi : ∀ b : 𝓞 E, IsIntegral (intAd F) (psi F E b) := by
    intro b
    obtain ⟨p, hp, hpb⟩ := RingOfIntegers.isIntegral b
    refine ⟨p.map (Int.castRingHom (intAd F)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (intAd F) (IntAf F E)).comp (Int.castRingHom (intAd F)))
        ((psi F E).comp (algebraMap ℤ (𝓞 E))),
      ← Polynomial.hom_eval₂, hpb, map_zero]
  let T : Subring (E ⊗[F] Af F) :=
    (integralClosure (intAd F) (IntAf F E)).toSubring.map (IntAf F E).subtype
  have hle : IntAf F E ≤ T := by
    show Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) ≤ T
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨_, hb⟩, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b, rfl⟩ := RingHom.mem_range.1 hb
      exact ⟨psi F E b, hpsi b, rfl⟩
    · exact ⟨algebraMap (intAd F) (IntAf F E) y, isIntegral_algebraMap, rfl⟩
  intro x
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

theorem intAdIncl_jacobson {x : intAd F} (hx : x ∈ Ideal.jacobson (⊥ : Ideal (intAd F))) :
    intAdIncl F E x ∈ Ideal.jacobson (⊥ : Ideal (IntAf F E)) := by
  unfold Ideal.jacobson at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  rintro M ⟨-, hM⟩
  have := hM
  exact hx _ ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ intAdIncl_isIntegral M⟩

theorem exists_map_psi_eq_span (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) :
    ∃ t : IntAf F E, IsUnit (t : E ⊗[F] Af F) ∧ 𝔞.map (psi F E) = Ideal.span {t} := by
  have hN0 : Ideal.absNorm 𝔞 ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNmem : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ 𝔞 := Ideal.absNorm_mem 𝔞
  have hNne : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ≠ 0 := by
    intro h0
    apply hN0
    have := congrArg (algebraMap (𝓞 E) E) h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  have hI : Ideal.span {((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E)} * 𝔞 ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hNne, h⟩
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (J := 𝔞)
    (Ideal.mul_le.2 fun _ _ _ hy => Ideal.mul_mem_left _ _ hy) hI
  obtain ⟨μ₀, hidem, hjac⟩ := exists_idem_intAd (F := F) ((Ideal.absNorm 𝔞 : ℕ) : intAd F)
  obtain ⟨t, ht⟩ := map_eq_span_of_idem (psi F E) 𝔞 (IsNoetherian.noetherian 𝔞) _ a hNmem ha
    (intAdIncl F E μ₀)
    (by simpa [map_mul] using congrArg (intAdIncl F E) hidem)
    (by simpa [map_mul, map_sub] using intAdIncl_jacobson (E := E) hjac)
  refine ⟨t, ?_, ht⟩
  have hmem : psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ Ideal.span {t} := by
    rw [← ht]
    exact Ideal.mem_map_of_mem _ hNmem
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
  have hu : IsUnit ((psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) : IntAf F E) : E ⊗[F] Af F) := by
    rw [map_natCast, SubringClass.coe_natCast, ← map_natCast (algebraMap F (E ⊗[F] Af F))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN0)).map _
  rw [← hs, Subring.coe_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem psi_mem_map_iff (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) (a : 𝓞 E) :
    psi F E a ∈ 𝔞.map (psi F E) ↔ a ∈ 𝔞 := by
  refine ⟨fun ha => ?_, fun ha => Ideal.mem_map_of_mem _ ha⟩
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
  have h𝔟0 : 𝔟 ≠ 0 := by
    rintro rfl
    rw [mul_zero, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at h𝔟
    exact hc0 h𝔟
  have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h0 => hc0 (RingOfIntegers.coe_injective (h0.trans (map_zero _).symm))
  have key : Ideal.span {a} * 𝔟 ≤ 𝔞 * 𝔟 := by
    rw [← h𝔟, Ideal.span_singleton_mul_le_iff]
    intro b hb
    have h1 : psi F E (a * b) ∈ Ideal.span {psi F E c} := by
      have h2 : psi F E (a * b) ∈ (𝔞 * 𝔟).map (psi F E) := by
        rw [map_mul, Ideal.map_mul]
        exact Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ hb)
      rwa [← h𝔟, Ideal.map_span, Set.image_singleton] at h2
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
    have hpsi : ∀ z : 𝓞 E, ((psi F E z : IntAf F E) : E ⊗[F] Af F) =
        inclE (F := F) (Af F) (algebraMap (𝓞 E) E z) := fun _ => rfl
    have e1 := congrArg (fun z : IntAf F E => (z : E ⊗[F] Af F)) hs
    simp only [Subring.coe_mul, hpsi] at e1
    have hq : inclE (F := F) (Af F) (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) =
        (s : E ⊗[F] Af F) := by
      have hu : IsUnit (inclE (F := F) (Af F) (algebraMap (𝓞 E) E c)) := (IsUnit.mk0 _ hcE).map _
      apply hu.mul_right_cancel
      rw [e1, ← map_mul, div_mul_cancel₀ _ hcE]
    have hint : IsIntegral ℤ (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) :=
      Formalism.UG.P.csGlob_int (F := F) _ (by rw [hq]; exact s.2)
    have hint' : algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c ∈ integralClosure ℤ E := hint
    obtain ⟨k, hk⟩ : ∃ k : 𝓞 E,
        algebraMap (𝓞 E) E k = algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c :=
      ⟨⟨_, hint'⟩, rfl⟩
    refine Ideal.mem_span_singleton'.2 ⟨k, RingOfIntegers.coe_injective ?_⟩
    rw [map_mul, hk]
    exact div_mul_cancel₀ _ hcE
  rw [← Ideal.dvd_iff_le, mul_dvd_mul_iff_right h𝔟0, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem] at key
  exact key

end

theorem extId_eq_map (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, (Subtype.ext hz).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem extId_principal_and_inter : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → (∃ t : IntAf I.F I.E, IsUnit (t : (I.E ⊗[I.F] Af I.F)) ∧ extId I 𝔞 = Ideal.span {t}) ∧ ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E), (⟨_, h⟩ : IntAf I.F I.E) ∈ extId I 𝔞 ↔ a ∈ 𝔞 := by
  intro I 𝔞 h𝔞
  rw [extId_eq_map]
  exact ⟨exists_map_psi_eq_span 𝔞 h𝔞, fun a _ => psi_mem_map_iff 𝔞 h𝔞 a⟩

end GlobalTheory.RowLev
end

