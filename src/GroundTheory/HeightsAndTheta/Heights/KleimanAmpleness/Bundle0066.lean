module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockGenDiagLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def BlockGen (S : Type*) [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  ∀ j : ι k₀, y ⟨k₀, j⟩ ≠ 0 → ∀ k, ∃ w : ι k → Ω,
    (∀ a b, y ⟨k, a⟩ * w b ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j)) ∧
      ∑ b, y ⟨k, b⟩ * w b = 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

section Points

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem exists_locIn_of_eq {A B : Subalgebra F Ω} (hAB : A = B) (p : Ideal A) (hp : p.IsPrime) :
    ∃ q : Ideal B, q.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn A p = IndefiniteRowSideFullHecke.Kleiman2.locIn B q := by
  subst hAB
  exact ⟨p, hp, rfl⟩

theorem chartRingOver_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) (c : Unit → κ') :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) c =
      chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) (fun u => σ (c u)) := by
  rw [SectionsOverLocalization.chartRingOver_oneBlock_eq, SectionsOverLocalization.chartRingOver_oneBlock_eq]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩


variable (F) in
theorem modelPts_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) := by
  ext z
  constructor
  · rintro ⟨c, hc, p, hp, rfl⟩
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq (chartRingOver_oneBlock_comp σ v c) p hp
    exact ⟨fun u => σ (c u), fun u => hc u, q, hq, he⟩
  · rintro ⟨c, hc, p, hp, rfl⟩
    have hc' : ∀ u, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ) ⟨u, σ.symm (c u)⟩ ≠ 0 := fun u => by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.oneBlock] using hc u
    have hch : chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) c =
        chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) (fun u => σ.symm (c u)) := by
      rw [chartRingOver_oneBlock_comp σ v]
      simp
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq hch p hp
    exact ⟨fun u => σ.symm (c u), hc', q, hq, he⟩


variable (F) in
theorem modelPts_eq_of_base {N : ℕ} {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K)
    (e : ι k₀ ≃ Fin (N + 1)) {K' : Type} {ι' : K' → Type} (y' : (Σ k, ι' k) → Ω) (k₀' : K')
    (e' : ι' k₀' ≃ Fin (N + 1)) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀)
    (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = IndefiniteRowSideFullHecke.Kleiman2.modelPts F y' := by
  rw [hy.2, hy'.2, ← modelPts_oneBlock_comp F e.symm, hx, modelPts_oneBlock_comp F e'.symm]

end Points

theorem veryAmple_change (hGen : ModelChangeGen.Statement) (F : Type) [Field F] (Ω : Type) [Field Ω]
    [Algebra F Ω] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1))
    (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm)
    (β : K → ℤ) (β' : K' → ℤ)
    (hs : ∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) :
    IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β' := by
  have h0 : secOver F y β = secOver F y' β' := by simpa using hs 0
  have hpts := modelPts_eq_of_base F y k₀ e y' k₀' e' hy hy' hx
  unfold IndefiniteRowSideFullHecke.Kleiman2.VeryAmple IndefiniteRowSideFullHecke.Kleiman2.SameModel
  rw [hpts]
  constructor
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    refine ⟨n, x', fun j => h0 ▸ hmem j, ?_, hsame⟩
    exact (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem).1 hgen
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    have hmem' : ∀ j, x' j ∈ secOver F y β := fun j => h0 ▸ hmem j
    exact ⟨n, x', hmem', (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem').2 hgen, hsame⟩

theorem VeryAmpleModel.proof (hVA : VeryAmpleEq.Statement) (hGen : ModelChangeGen.Statement) :
    VeryAmpleModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hxe hmod Q β hQ
  subst hxe
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (Q.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen Q n g := hg
  have hmod' := GraphModel.full F N Ω _ Q n (r + 1) g hx hgen
  have hsec := realises_graph Q n g hgen
  rw [hVA F N Ω _ Q n (r + 1) g hgen]
  exact (veryAmple_change hGen F Ω N K ι y k₀ e (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock
    (Equiv.refl _) hmod hmod' rfl β (graphDeg n) (fun c => (hQ c).symm.trans (hsec c))).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowSmulEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded)

namespace SectionMapInj

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def chartMon (S : Type) [CommRing S] (c : ∀ k, ι k) : MRingOver S ι :=
  ∏ k, X ⟨k, c k⟩

def chartCell (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem dvd_pow_of_mem_cellMon (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) :
    ∃ n : ℕ, t ∣ chartMon S c ^ n := by
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [show i = c k from Finset.mem_singleton.mp hi]
    exact ⟨1, by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)⟩
  | one => exact ⟨0, one_dvd _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [pow_add]; exact mul_dvd_mul hm hn⟩

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]

theorem pow_smul_eq_zero_of_le {r : MRingOver S ι} {y : M} {m n : ℕ} (h : r ^ m • y = 0) (hmn : m ≤ n) :
    r ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) {y : M}
    (hy : t • y = 0) : ∃ n : ℕ, chartMon S c ^ n • y = 0 := by
  obtain ⟨n, q, hq⟩ := dvd_pow_of_mem_cellMon c ht
  exact ⟨n, by rw [hq, mul_comm, mul_smul, hy, smul_zero]⟩

theorem exists_chart_dvd (N : ℕ) (μ : (Σ k, ι k) →₀ ℕ) (r : S)
    (hμ : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩) :
    ∃ c : ∀ k, ι k, chartMon S c ^ N ∣ (monomial μ r : MRingOver S ι) := by
  classical
  have hex : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hne
    simp only [not_exists, not_le] at hne
    have hle : ∑ i, μ ⟨k, i⟩ ≤ ∑ _i : ι k, N := Finset.sum_le_sum fun i _ => (hne i).le
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have := hμ k
    omega
  choose c hc using hex
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun q => pow_zero _), Fintype.prod_sigma, chartMon,
    ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRingOver S ι) ^ μ ⟨k, i⟩)
    (Finset.mem_univ (c k)))

variable [Module S M] [IsScalarTower S (MRingOver S ι) M]

def killedSet (𝓜 : (K → ℤ) → Submodule S M) : Set M :=
  {y | (∃ d, y ∈ 𝓜 d) ∧ ∃ n : ℕ, ∀ c : ∀ k, ι k, chartMon S c ^ n • y = 0}

theorem bound_finset (𝓜 : (K → ℤ) → Submodule S M) (F : Finset M) (hF : (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜) :
    ∃ (D : ℤ) (N : ℕ), ∀ f ∈ F, ∃ d : K → ℤ, f ∈ 𝓜 d ∧ (∀ k, d k ≤ D) ∧
      ∀ c : ∀ k, ι k, chartMon S c ^ N • f = 0 := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty => intro _; exact ⟨0, 0, by simp⟩
  | insert a F ha ih =>
    intro hF
    rw [Finset.coe_insert, Set.insert_subset_iff] at hF
    obtain ⟨D, N, hDN⟩ := ih hF.2
    obtain ⟨⟨d, hd⟩, n, hn⟩ := hF.1
    refine ⟨max D (∑ k, |d k|), max N n, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · refine ⟨d, hd, fun k => ?_, fun c => pow_smul_eq_zero_of_le (hn c) (le_max_right _ _)⟩
      exact ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |d k|) (fun l _ => abs_nonneg _)
        (Finset.mem_univ k))).trans (le_max_right _ _)
    · obtain ⟨e, he, heD, heN⟩ := hDN f hf
      exact ⟨e, he, fun k => (heD k).trans (le_max_left _ _),
        fun c => pow_smul_eq_zero_of_le (heN c) (le_max_left _ _)⟩

theorem exists_finset_span [IsNoetherian (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) :
    ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧
      ∀ y ∈ killedSet (ι := ι) 𝓜, y ∈ Submodule.span (MRingOver S ι) (↑F : Set M) := by
  classical
  obtain ⟨W, ⟨F, hFH, rfl⟩, hmax⟩ := (set_has_maximal_iff_noetherian (R := MRingOver S ι) (M := M)).mpr ‹_›
    {W | ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧ W = Submodule.span (MRingOver S ι) (↑F : Set M)}
    ⟨_, ∅, by simp, rfl⟩
  refine ⟨F, hFH, fun y hy => ?_⟩
  by_contra hn
  refine hmax (Submodule.span _ ↑(insert y F)) ⟨insert y F, ?_, rfl⟩ ?_
  · rw [Finset.coe_insert]; exact Set.insert_subset hy hFH
  · refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun h => hn ?_
    rw [h]; exact Submodule.subset_span (by simp)

end SectionMapInj

theorem SectionMapInj.full : SectionMapInj.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hS hfin hM
  classical
  have := hS
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨F, hFH, hspan⟩ := SectionMapInj.exists_finset_span (ι := ι) 𝓜
  obtain ⟨D, N, hDN⟩ := SectionMapInj.bound_finset (ι := ι) 𝓜 F hFH
  set L : ℕ := ∑ k, Fintype.card (ι k) with hL
  refine ⟨D + L * N + 1, fun c hc x hx hloc => ?_⟩
  have hxH : x ∈ SectionMapInj.killedSet (ι := ι) 𝓜 := by
    refine ⟨⟨c, hx⟩, ?_⟩
    have hch : ∀ ch : ∀ k, ι k, ∃ n : ℕ, SectionMapInj.chartMon S ch ^ n • x = 0 := by
      intro ch
      have h := hloc (SectionMapInj.chartCell ch)
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      rw [one_smul, one_smul, smul_zero] at hu
      exact SectionMapInj.exists_pow_smul_eq_zero ch u.2 hu
    choose n hn using hch
    exact ⟨Finset.univ.sup n, fun ch =>
      SectionMapInj.pow_smul_eq_zero_of_le (hn ch) (Finset.le_sup (Finset.mem_univ ch))⟩
  obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp (hspan x hxH)
  have hV : x ∈ ⨆ (e : K → ℤ) (_ : e ≠ c), 𝓜 e := by
    rw [← hg]
    refine Submodule.sum_mem _ fun f hf => ?_
    obtain ⟨d, hfd, hdD, hfN⟩ := hDN f hf
    rw [MvPolynomial.as_sum (g f), Finset.sum_smul]
    refine Submodule.sum_mem _ fun μ _ => ?_
    set a : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩ with ha
    have hhom : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial μ (AddMonoidAlgebra.coeff (g f) μ) : MRingOver S ι) a := fun m hm k => by
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have hmem := hM.2 a d _ f hhom hfd
    by_cases he : (d + fun k => (a k : ℤ)) = c
    · have hdeg : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩ := by
        intro k
        have h1 := congrFun he k
        have h2 := hc k
        have h3 := hdD k
        have h4 : Fintype.card (ι k) ≤ L :=
          Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h5 : ((Fintype.card (ι k) * N : ℕ) : ℤ) ≤ ((L * N : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right _ h4
        simp only [Pi.add_apply] at h1
        push_cast at h5
        have h6 : ((Fintype.card (ι k) * N + 1 : ℕ) : ℤ) ≤ (a k : ℤ) := by push_cast; linarith
        exact_mod_cast h6
      obtain ⟨ch, q, hq⟩ := SectionMapInj.exists_chart_dvd (S := S) N μ (AddMonoidAlgebra.coeff (g f) μ) hdeg
      rw [hq, mul_comm, mul_smul, hfN ch, smul_zero]
      exact Submodule.zero_mem _
    · exact (le_iSup₂ (f := fun (e : K → ℤ) (_ : e ≠ c) => 𝓜 e) _ he) hmem
  exact Submodule.disjoint_def.mp (hM.1.submodule_iSupIndep c) x hx hV

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)

theorem RealiseRestrict.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement)
    (hR : ResidueMap.Statement) (hRG : ResidueGen.Statement) (hC : RestrictGen.Statement) :
    RealiseRestrict.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy Q β hQ K' _ _ y' hy' hI hxy
  subst hx
  obtain ⟨Q'', hQ''⟩ := BundleOfDeg.full F K ι K' y' k₀ N e hy' β
  obtain ⟨ca, hca⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨cb, hcb⟩ := Kleiman.Generated.full F K' N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) Q''
  obtain ⟨cg, hcg⟩ := hG F K ι Ω y k₀ hy β
  obtain ⟨c, hcA, hcB, hcG⟩ : ∃ c, ca ≤ c ∧ cb ≤ c ∧ cg ≤ c :=
    ⟨max ca (max cb cg), by omega, by omega, by omega⟩
  obtain ⟨R, σ, hfr, hblk, hch⟩ := hR F K ι Ω y K' y' hI
  choose d₀ hd₀ using hy'.1
  obtain ⟨ρ, hρ1, hρ2⟩ := hRG F K ι Ω y K' y' hI R σ hfr hch (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (hcg c hcG) d₀ hd₀

  have hT : ∀ t : K', t ∈ secOver F y' (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm),
        t ∈ Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
          (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := by
    intro t
    have h := hS F K ι K' y' k₀ N e _ rfl hy' (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) 0 t
    simp only [PowRealises.twistMod_zero, mul_one, Submodule.mem_iInf, Submodule.restrictScalars_mem,
      neg_zero, zpow_zero] at h
    rw [h, PowRealises.mem_secOver]
    refine forall_congr' fun cc => forall_congr' fun hc => ?_
    rw [hρ2 cc hc, PowRealises.mem_span_inv_iff _
      (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))]
  have hQgen : ∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
        (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := fun I => by
    rw [← hca c hcA I, hQ c]
  have hQ''gen : ∀ I, (Q''.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
        (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := fun I => by
    rw [← hcb c hcB I, hQ'' c]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hT t).mp ht I
    · rw [Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ((hT t).mpr fun J => Submodule.subset_span ht)

  have hfx : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
      aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g ≠ 0 →
      ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g ∈ R,
        σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) f /
          aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g := by
    intro f g m hf hg hg0
    obtain ⟨h, hh⟩ := hblk k₀ (rename e.symm f) (rename e.symm g) m hf.rename_isHomogeneous
      hg.rename_isHomogeneous (by rwa [aeval_rename])
    have ea : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm f) /
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm g) =
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g := by
      rw [aeval_rename, aeval_rename]
    refine ⟨ea ▸ h, ?_⟩
    have hsub : (⟨_, ea ▸ h⟩ : R) = ⟨_, h⟩ := Subtype.ext ea.symm
    rw [hsub, hh, aeval_rename, aeval_rename]
  have hw' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  obtain ⟨r, hr⟩ := hC F N Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) K' (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) hxy
    R σ hfx Q Q'' c (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ρ
    (∏ k, y ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k))
    (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) hw' hQgen hQ''gen hρ1
  exact ⟨Q'', r, hr, hQ''⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ChartKernel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (Ω : Type) [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (Ω' : Type) [Field Ω'] [Algebra S Ω'] (y' : (Σ k, ι k) → Ω'),
    mIdealOver S y ≤ mIdealOver S y' → ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∀ g : MvPolynomial (Σ k, ι k) S, aeval (fun p => y p / y ⟨p.1, c p.1⟩) g = 0 →
        aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleTwistVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

theorem twistVanishAll_closed : Kleiman.TwistVanishAll.Statement.{0, 0} :=
  Kleiman.TwistVanishAll.proof Kleiman.Extension.full Kleiman.SerreVanish.full Kleiman.TwistSplit.proof

theorem lineBundle_twist_vanish {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (Q : Kleiman.LineBundle F x) :
    ∃ c₀ : ℤ, ∀ (i : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton ((Q.twist (Kleiman.twistSys F x c)).H i) := by
  obtain ⟨c₀, hc₀⟩ := twistVanishAll_closed F Ω N x Q (Kleiman.twistBundle F x 1) N x
    Kleiman.mem_secs_twistBundle_one Kleiman.span_range_eq_twistMod_one
  refine ⟨c₀, fun i c hi hc => ?_⟩
  have h := hc₀ i 0 c hi hc
  have e : Q.twist ((Kleiman.twistBundle F x 1).pow 0) = Q.toSubSystem :=
    Kleiman.SubSystem.twist_twistSys_zero _
  rwa [e] at h

theorem RayVanish.proof (hMC : ModelCechTwist.Statement) : RayVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ hM β
  have : Nonempty (ι k₀) := let ⟨i, _⟩ := hM.1 k₀; ⟨i⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := lineBundle_twist_vanish Q
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun c hc i hi => ?_⟩
  obtain ⟨φ⟩ := hMC F K ι Ω y k₀ N e hM β Q hQ 1 1 0 c i
  have hdeg : (1 : ℕ) • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β 1 0 + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ =
      β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL]
  have hsys : (Kleiman.twistMul Q.toSubSystem 1 0).pow 1 = Q.toSubSystem := by
    change (Kleiman.twistSys _ _ 0).twist (Kleiman.twistMul Q.toSubSystem 1 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.twistMul]
    change ((Kleiman.twistSys _ _ 0).twist Q.toSubSystem).twist (Kleiman.twistSys _ _ 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.SubSystem.twist_twistSys_zero]
  rw [hdeg, hsys] at φ
  have := hc₀ i c hi (by omega)
  exact φ.symm.toEquiv.subsingleton

theorem RayVanish.proof_of_ties (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) :
    RayVanish.Statement :=
  RayVanish.proof (ModelCechTwist.proof (ChartSecMul.proof BundleOfDeg.full) BaseRealises.proof hLoc hRef)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

