module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

section

variable {k : Type} [Field k] {N m : ℕ}

theorem weight_mapDomain_base (e : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (graphIdx N m))
        (Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e) =
      Sum.elim (fun _ => e.degree) (fun _ => 0) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  funext c
  rw [← sum_block_eq_blockWeight]
  rcases c with ⟨⟩ | ⟨⟩
  · simp only [Sum.elim_inl]
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl fun a _ => Finsupp.mapDomain_apply_of_injective hinj e a
  · simp only [Sum.elim_inr]
    refine Finset.sum_eq_zero fun b _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨a, ha⟩
    cases (Sigma.mk.inj ha).1

theorem rename_base_homogeneousComponent (d : ℕ) (f : Kleiman.Poly k N) :
    rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (homogeneousComponent d f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (Sum.elim (fun _ => d) (fun _ => 0))
        (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj, coeff_homogeneousComponent,
      weight_mapDomain_base]
    by_cases hd : e.degree = d
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (congrFun h (Sum.inl ()))]
  · push Not at he
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

end

theorem CurveComap.proof (hR : SectionRatio.Statement) (hD : RatioDim.Statement) : CurveComap.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle e
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
  have hdim := hD k N m W hW.isPrime hW.multiHomog j hj fun b => by
    obtain ⟨d, f, g, -, -, h1, h2⟩ := hR k N Ω x Q n m s hx hgen W hW hle j b hj
    exact ⟨f, g, h1, h2⟩
  have hsub : Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) e ↔
      ringKrullDim (Kleiman.Poly k N ⧸
          W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) =
        ((e + 1 : ℕ) : WithBot ℕ∞) := by
    refine ⟨fun h => h.dim, fun h => ⟨Ideal.comap_isPrime _ _, fun f hf d => ?_, ?_, ?_, h⟩⟩
    · rw [Ideal.mem_comap] at hf ⊢
      rw [rename_base_homogeneousComponent]
      exact hW.multiHomog _ hf _
    · rw [← comap_mIdealOver_graph (S := k) x s]
      exact Ideal.comap_mono hle
    · obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
      have hXi : rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i : Kleiman.Poly k N) =
          X ⟨baseBlock, i⟩ := rename_X _ _
      exact ⟨i, by rw [Ideal.mem_comap, hXi]; exact hi⟩
  rw [hsub, FieldNumbers.CutRegular.relDim_eq_natCast_iff, hdim, Fintype.card_sum, Fintype.card_unit]
  generalize ringKrullDim (Kleiman.Poly k N ⧸
    W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) = D
  induction D using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe t =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj,
      WithBot.coe_inj]
    induction t using ENat.recTopCoe with
    | top => exact iff_of_false (by rw [top_add]; exact ENat.top_ne_natCast _) (ENat.top_ne_natCast _)
    | coe t =>
      norm_cast
      omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SgnSingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

namespace CechContract

section Comb

variable {n : ℕ} {M : Type*} [AddCommGroup M]

theorem sgn_insert {J : Finset (Fin n)} {a : Fin n} (ha : a ∉ J) (j : Fin n) :
    Kleiman.Cech.sgn (insert a J) j = if a < j then -Kleiman.Cech.sgn J j else Kleiman.Cech.sgn J j := by
  unfold Kleiman.Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ]; ring
  · rfl

theorem sgn_mul_self (J : Finset (Fin n)) (j : Fin n) : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn J j = 1 := by
  unfold Kleiman.Cech.sgn
  rw [← mul_pow]; norm_num

theorem sgn_singleton (j : Fin n) : Kleiman.Cech.sgn {j} j = 1 := by
  rw [Kleiman.Cech.sgn, Finset.filter_singleton, if_neg (lt_irrefl j)]; simp

def cD (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  ∑ j ∈ J, Kleiman.Cech.sgn J j • f (J.erase j)

def cH (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  if j₀ ∈ J then 0 else Kleiman.Cech.sgn (insert j₀ J) j₀ • f (insert j₀ J)

theorem cD_cH_add (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) :
    cD (cH j₀ f) J + cH j₀ (cD f) J = f J := by
  by_cases h₀ : j₀ ∈ J
  · have hH : cH j₀ (cD f) J = 0 := if_pos h₀
    have hrest : ∑ j ∈ J.erase j₀, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hj, -⟩ := Finset.mem_erase.mp hj
      rw [cH, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hj, h₀⟩), smul_zero]
    rw [hH, add_zero, cD, ← Finset.add_sum_erase J _ h₀, hrest, add_zero, cH,
      if_neg (Finset.notMem_erase j₀ J), Finset.insert_erase h₀, smul_smul, sgn_mul_self, one_smul]
  · have hsum : ∑ j ∈ J, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) +
        ∑ j ∈ J, Kleiman.Cech.sgn (insert j₀ J) j₀ • Kleiman.Cech.sgn (insert j₀ J) j •
          f ((insert j₀ J).erase j) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj₀ : j ≠ j₀ := fun h => h₀ (h ▸ hj)
      have hn : j₀ ∉ J.erase j := fun h => h₀ (Finset.mem_of_mem_erase h)
      have e : insert j₀ (J.erase j) = (insert j₀ J).erase j := (Finset.erase_insert_of_ne (Ne.symm hj₀)).symm
      have s1 : Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ = Kleiman.Cech.sgn (J.erase j) j₀ := by
        rw [← e, sgn_insert hn, if_neg (lt_irrefl _)]
      have s2 : Kleiman.Cech.sgn (insert j₀ J) j₀ = Kleiman.Cech.sgn J j₀ := by
        rw [sgn_insert h₀, if_neg (lt_irrefl _)]
      have s3 := sgn_insert h₀ j
      have s4 : Kleiman.Cech.sgn J j₀ =
          if j < j₀ then -Kleiman.Cech.sgn (J.erase j) j₀ else Kleiman.Cech.sgn (J.erase j) j₀ := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact sgn_insert (Finset.notMem_erase j J) j₀
      have hc : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ +
          Kleiman.Cech.sgn (insert j₀ J) j₀ * Kleiman.Cech.sgn (insert j₀ J) j = 0 := by
        rw [s1, s2, s3, s4]
        rcases lt_or_gt_of_ne hj₀ with h | h
        · rw [if_neg (lt_asymm h), if_pos h]; ring
        · rw [if_pos h, if_neg (lt_asymm h)]; ring
      rw [cH, if_neg hn, e, smul_smul, smul_smul, ← add_smul, hc, zero_smul]
    have hH : cH j₀ (cD f) J = Kleiman.Cech.sgn (insert j₀ J) j₀ • cD f (insert j₀ J) := if_neg h₀
    rw [hH]
    unfold cD
    rw [Finset.sum_insert h₀, Finset.erase_insert h₀, smul_add, smul_smul, sgn_mul_self, one_smul,
      Finset.smul_sum, add_left_comm, hsum, add_zero]

end Comb

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}


open Classical in
noncomputable def extZ {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (K : Finset (Fin (N + 1))) : Ω :=
  if h : K.Nonempty ∧ K ⊆ Kleiman.support x ∧ K.card = p + 1 then s ⟨⟨K, h.1, h.2.1⟩, h.2.2⟩ else 0

theorem extZ_idx {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : extZ s I.1.1 = s I := by
  rw [extZ, dite_eq_left ⟨I.1.2.1, I.1.2.2, I.2⟩]

theorem d_eq {p : ℕ} (t : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p) (g : Finset (Fin (N + 1)) → Ω)
    (hg : ∀ I, t I = g I.1.1) (J : Kleiman.Cech.Idx (Kleiman.support x) (p + 1)) :
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t J = cD g J.1.1 := by
  rw [Kleiman.Cech.d_apply, cD,
    ← Finset.sum_coe_sort J.1.1 (fun j => Kleiman.Cech.sgn J.1.1 j • g (J.1.1.erase j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ • t (Kleiman.Cech.face J j) = _ • g (Kleiman.Cech.face J j).1.1
  rw [hg]

def insIdx {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ} (I : Kleiman.Cech.Idx (Kleiman.support x) p)
    (h : j₀ ∉ I.1.1) : Kleiman.Cech.Idx (Kleiman.support x) (p + 1) :=
  ⟨⟨insert j₀ I.1.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀ I.1.2.2⟩, by
    rw [Finset.card_insert_of_notMem h, I.2]⟩

theorem cH_cD_extZ {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ}
    (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (hds : Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p s = 0)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : cH j₀ (cD (extZ s)) I.1.1 = 0 := by
  unfold cH
  split_ifs with h
  · rfl
  · have h1 := d_eq S s (extZ s) (fun I => (extZ_idx s I).symm) (insIdx hj₀ I h)
    rw [hds] at h1
    change _ • cD (extZ s) (insIdx hj₀ I h).1.1 = 0
    rw [← h1, Pi.zero_apply, smul_zero]

end CechSide

theorem proof : Statement := by
  intro S _ Ω _ _ N x G J₀ hcard hmono hadd
  obtain ⟨j₀, hJ₀⟩ := Finset.card_eq_one.mp hcard
  have hj₀U : j₀ ∈ Kleiman.support x := J₀.2.2 (hJ₀ ▸ Finset.mem_singleton_self j₀)
  have hG : ∀ J J' : Kleiman.Chart x, J'.1 = insert j₀ J.1 → G J' = G J := fun J J' h =>
    hadd J J' (by rw [h, hJ₀, Finset.insert_eq])
  refine ⟨fun J => ?_, fun s hs hds => ?_, fun p s hs hds => ?_⟩
  · let J' : Kleiman.Chart x := ⟨insert j₀ J.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀U J.2.2⟩
    rw [← hG J J' rfl]
    exact hmono J₀ J' (by
      rw [hJ₀]; exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  · refine ⟨s ⟨J₀, hcard⟩, (hs ⟨J₀, hcard⟩ (Set.mem_univ _) :), fun J => ?_⟩
    have eb : extZ s {j₀} = s ⟨J₀, hcard⟩ :=
      (congrArg (extZ s) hJ₀).symm.trans (extZ_idx s ⟨J₀, hcard⟩)
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp J.2
    have e1 : cD (cH j₀ (extZ s)) J.1.1 = extZ s {j₀} := by
      rw [hj, cD, Finset.sum_singleton, Finset.erase_singleton, sgn_singleton, one_smul, cH,
        if_neg (Finset.notMem_empty _), insert_empty_eq, sgn_singleton, one_smul]
    rw [← extZ_idx s J, ← cD_cH_add j₀ (extZ s) J.1.1, cH_cD_extZ S hj₀U s hds J, add_zero, e1, eb]
  · refine ⟨fun I => cH j₀ (extZ s) I.1.1, fun I _ => ?_, ?_⟩
    · show cH j₀ (extZ s) I.1.1 ∈ G I.1
      unfold cH
      split_ifs with h
      · exact zero_mem _
      · have hK : s (insIdx hj₀U I h) ∈ G (insIdx hj₀U I h).1 := hs _ (Set.mem_univ _)
        rw [← extZ_idx s (insIdx hj₀U I h), hG I.1 (insIdx hj₀U I h).1 rfl] at hK
        exact zsmul_mem hK _
    · funext J
      rw [d_eq S _ (cH j₀ (extZ s)) (fun _ => rfl)]
      have := cD_cH_add j₀ (extZ s) J.1.1
      rw [cH_cD_extZ S hj₀U s hds J, add_zero, extZ_idx] at this
      exact this

end CechContract

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SpanSecsMemLocInSelf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Local

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem spanSecs_mem_locIn_self {A : Subalgebra F Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

theorem spanSecs_mul_step {B : Subalgebra F Ω} {q : Ideal B} [hq : q.IsPrime] {T : Set Ω} {u g : Ω}
    (hg : g ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (hu : ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * (g * u) ∈ Submodule.span B T := by
  obtain ⟨b, hb, hbu⟩ := hu
  obtain ⟨a, b', hb', rfl⟩ := mem_locIn.mp hg
  refine ⟨b' * b, fun h => (hq.mem_or_mem h).elim hb' hb, ?_⟩
  have h0 := coe_ne_zero_of_not_mem hb'
  have e : ((b' * b : B) : Ω) * ((a : Ω) / b' * u) = a • ((b : Ω) * u) := by
    rw [Subalgebra.smul_def, smul_eq_mul, Subalgebra.coe_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ hbu

theorem spanSecs_exists_mul_mem (B C : Subalgebra F Ω) (q : Ideal B) [hq : q.IsPrime]
    (hC : ∀ a ∈ C, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (T : Set Ω) {u : Ω} (hu : u ∈ Submodule.span C T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T := by
  induction hu using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_not_mem_of_prime hq, by simpa using Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_not_mem_of_prime hq, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨b₁, hb₁, h₁⟩ := hz
    obtain ⟨b₂, hb₂, h₂⟩ := hw
    refine ⟨b₁ * b₂, fun h => (hq.mem_or_mem h).elim hb₁ hb₂, ?_⟩
    have e : ((b₁ * b₂ : B) : Ω) * (z + w) = b₂ • ((b₁ : Ω) * z) + b₁ • ((b₂ : Ω) * w) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul a z _ hz =>
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact spanSecs_mul_step (hC _ a.2) hz

theorem spanSecs_mem_of_local (B : Subalgebra F Ω) (T : Set Ω) (u : Ω)
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    u ∈ Submodule.span B T := by
  let J : Ideal B := (Submodule.span B T).comap (LinearMap.toSpanSingleton B Ω u)
  have hJ : ∀ b : B, b ∈ J ↔ (b : Ω) * u ∈ Submodule.span B T := fun b => Iff.rfl
  by_cases hJt : J = ⊤
  · have h1 : (1 : B) ∈ J := hJt ▸ Submodule.mem_top
    simpa using (hJ 1).mp h1
  · obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hJt
    obtain ⟨b, hb, hbu⟩ := h q hq
    exact absurd (hJq ((hJ b).mpr hbu)) hb

end Local

theorem SpanSecs.proof : SpanSecs.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod T d s
  have hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩ := fun i => by rw [hx]; rfl

  let B : ι k₀ → Subalgebra F Ω := fun i' =>
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => i')
  have hB : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), Kleiman.chartRing F x (Kleiman.singleChart hi) = B (e.symm i) := by
    intro i hi
    rw [← chartRingOver_oneBlock_eq_chartRing (S := F) x (fun _ => i) hi]
    unfold B chartRingOver
    congr 1
    ext z
    constructor
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e.symm l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩

  have hBc : ∀ c : ∀ k, ι k, B (c k₀) ≤ chartRingOver F y c := by
    intro c
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨_, l⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, l⟩, rfl⟩
  constructor
  · intro hs c hc
    have hi : x (e (c k₀)) ≠ 0 := by rw [hxv, Equiv.symm_apply_apply]; exact hc k₀
    set A := Kleiman.chartRing F x (Kleiman.singleChart hi) with hA
    have hAc : A ≤ chartRingOver F y c := by
      rw [hA, hB, Equiv.symm_apply_apply]; exact hBc c
    have hs' := Submodule.mem_iInf _ |>.mp hs (Kleiman.singleChart hi)
    rw [Submodule.restrictScalars_mem,
      Kleiman.twistMod_eq_span d _ (Finset.mem_singleton_self (e (c k₀)))] at hs'
    have hv : y ⟨k₀, c k₀⟩ = x (e (c k₀)) := by rw [hxv, Equiv.symm_apply_apply]
    rw [hv]
    refine Submodule.mul_induction_on hs' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have e1 : m * (a • x (e (c k₀)) ^ d) * x (e (c k₀)) ^ (-d) = (⟨a, hAc a.2⟩ : chartRingOver F y c) • m := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, zpow_neg]
        field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (span_subset_span hAc T hm)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  · intro h
    refine Submodule.mem_iInf _ |>.mpr fun I => ?_
    rw [Submodule.restrictScalars_mem]
    obtain ⟨i, hiI⟩ := I.2.1
    have hi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hiI)
    rw [Kleiman.twistMod_eq_span d I hiI]
    have hle : Kleiman.chartRing F x (Kleiman.singleChart hi) ≤ Kleiman.chartRing F x I :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hiI)

    suffices key : s * x i ^ (-d) ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.singleChart hi)) T by
      have e1 : s = s * x i ^ (-d) * x i ^ d := by
        rw [zpow_neg, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero d hi), mul_one]
      rw [e1]
      exact Submodule.mul_mem_mul (span_subset_span hle T key) (Submodule.subset_span rfl)
    rw [hB i hi]
    have hxi' : y ⟨k₀, e.symm i⟩ ≠ 0 := by rw [← hxv]; exact hi
    refine spanSecs_mem_of_local _ T _ fun q hq => ?_
    have := hq.isPrime

    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q ∈
        IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
      ⟨fun _ => e.symm i, fun _ => hxi', q, hq.isPrime, rfl⟩
    rw [← hmod.2] at hz
    obtain ⟨c, hc, p, hp, hzp⟩ := hz
    have := hp
    have hCz : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      intro a ha
      rw [hzp]
      exact spanSecs_mem_locIn_self ha

    set w := y ⟨k₀, c k₀⟩ with hw
    set v := y ⟨k₀, e.symm i⟩ with hvdef
    have hw0 : w ≠ 0 := hc k₀
    have h1 : w / v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      spanSecs_mem_locIn_self (Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩)
    have h2 : v / w ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      hCz _ (Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩)
    have hg : (w / v) ^ d ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
      · rw [zpow_natCast]; exact pow_mem h1 n
      · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem h2 n
    have e2 : s * x i ^ (-d) = (w / v) ^ d * (s * w ^ (-d)) := by
      rw [hxv, ← hvdef, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e2]
    exact spanSecs_mul_step hg (spanSecs_exists_mul_mem _ _ q hCz T (h c hc))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

