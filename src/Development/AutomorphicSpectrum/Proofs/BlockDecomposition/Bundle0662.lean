module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHeckeSum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGenLt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0650

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodisationBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem maj_add_le (θ : InfFam D) (K K₀ : Set (Mx D ρ p)) (N : ℕ) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ R) (g w : Mx D ρ p) (hw : w ∈ K₀) :
    GlobalTheory.Unf.maj θ K N (g + w) ≤ (1 + R) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N g := by
  by_cases hb : GlobalTheory.Unf.InBox K (g + w)
  · have hb' : GlobalTheory.Unf.InBox (K + (-K₀)) g := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨k + -w, Set.add_mem_add hk (Set.neg_mem_neg.2 hw), ?_⟩
      have e : g - (k + -w) = g + w - k := by abel
      rw [e]; exact h0
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h0 := GlobalTheory.Unf.realSize_nonneg θ g
    have h1 := GlobalTheory.Unf.realSize_nonneg θ (g + w)
    have h2 : 1 + GlobalTheory.Unf.realSize θ g ≤ (1 + R) * (1 + GlobalTheory.Unf.realSize θ (g + w)) := by
      have h3 := GlobalTheory.MajSum.realSize_add_le θ (g + w) (-w)
      rw [add_neg_cancel_right] at h3
      have h4 := hR w hw
      nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ g) ^ N := by positivity
    have h5 : (1 + GlobalTheory.Unf.realSize θ g) ^ N ≤ (1 + R) ^ N * (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h2 N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp hq, one_mul]
    exact h5
  · have h0 : GlobalTheory.Unf.maj θ K N (g + w) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N g)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) :
    Continuous (GlobalTheory.Unf.realSize θ : Mx D ρ p → ℝ) := by
  unfold GlobalTheory.Unf.realSize
  refine continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_
  exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ ρ p).matrix_elem i j).norm

theorem periodisation_bound : ∀ {D : D7} {ρ p : ℕ} (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p,
    ∃ B : ℝ, ∀ y : Mx D ρ p,
      Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧
      ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B := by
  intro D ρ p θ hθ φ hφ
  obtain ⟨-, K, hK, hbd⟩ := GlobalTheory.SchwartzMaj.hasMaj_of_mem hθ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ ρ p
  obtain ⟨i1, -, -, -, -, K₀, hK₀, hcov⟩ := lattice_Mx D ρ p
  obtain ⟨C, hC⟩ := hbd N
  have hK' : IsCompact (K + (-K₀)) := hK.add hK₀.neg
  obtain ⟨R₀, hR₀⟩ := hK₀.exists_bound_of_continuousOn (f := fun w => GlobalTheory.Unf.realSize θ (-w))
    ((continuous_realSize hθ).comp continuous_neg).continuousOn
  have hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ |R₀| := fun w hw =>
    (le_abs_self _).trans ((hR₀ w hw).trans (le_abs_self _))
  have hg : Summable fun γ : ratMx D ρ p => GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p) := by
    have h := ENNReal.summable_toReal (hN _ hK')
    refine h.congr fun γ => ?_
    exact ENNReal.toReal_ofReal (GlobalTheory.Unf.maj_nonneg θ _ N _)
  set c : ℝ := |C| * (1 + |R₀|) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c * ∑' γ : ratMx D ρ p, GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p), fun y => ?_⟩
  obtain ⟨γ, hγ, hy⟩ := hcov y
  obtain ⟨ξ₀, rfl⟩ := mem_ratMx.1 hγ
  let e : Matrix (Fin ρ) (Fin p) D.host.E → ratMx D ρ p := fun ξ => ⟨rat (ξ - ξ₀), rat_mem _⟩
  have he : Function.Injective e := fun a b h => by
    have := rat_injective (congrArg Subtype.val h)
    exact sub_left_injective this
  have key : ∀ ξ, ‖φ (rt ξ + y)‖ ≤ c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by
    intro ξ
    have e1 : rt ξ + y = rat (ξ - ξ₀) + (rat ξ₀ + y) := by
      have : rat (ξ - ξ₀) = rt ξ - rat ξ₀ := by
        ext i j
        simp [rat, rt]
      rw [this]; abel
    rw [e1]
    refine (hC _).trans ?_
    have h1 := maj_add_le θ K K₀ N |R₀| (abs_nonneg _) hR (rat (ξ - ξ₀)) (rat ξ₀ + y) hy
    calc C * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y))
        ≤ |C| * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ _ N _)
      _ ≤ |C| * ((1 + |R₀|) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N (rat (ξ - ξ₀))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by rw [hc, mul_assoc]
  have hs' : Summable fun ξ => c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) :=
    (hg.comp_injective he).mul_left c
  have hs : Summable fun ξ => ‖φ (rt ξ + y)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hs'
  refine ⟨hs, (hs.tsum_le_tsum key hs').trans ?_⟩
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  exact tsum_comp_le_tsum_of_inj hg (fun _ => GlobalTheory.Unf.maj_nonneg θ _ N _) he

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductIntegral
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActCore

theorem relIndex_ne_of_out {G : Type} [Group G] (L K : Subgroup G) (hLK : L ≤ K)
    (h : {q : G ⧸ L | q.out ∈ K}.Finite) : L.relIndex K ≠ 0 := by
  have hmem : ∀ c : K ⧸ L.subgroupOf K, (((c.out : K) : G) : G ⧸ L).out ∈ K := by
    intro c
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul L ((c.out : K) : G)
    rw [ht]
    exact mul_mem (c.out).2 (hLK t.2)
  have hinj : Function.Injective (fun c : K ⧸ L.subgroupOf K =>
      (⟨(((c.out : K) : G) : G ⧸ L), hmem c⟩ : {q : G ⧸ L | q.out ∈ K})) := by
    intro a b hab
    have h1 : (((a.out : K) : G) : G ⧸ L) = (((b.out : K) : G) : G ⧸ L) :=
      congrArg Subtype.val hab
    have h2 : ((a.out : K) : G)⁻¹ * ((b.out : K) : G) ∈ L := QuotientGroup.eq.1 h1
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using h2
  haveI := h.to_subtype
  haveI : Finite (K ⧸ L.subgroupOf K) := Finite.of_injective _ hinj
  exact Subgroup.index_ne_zero_of_finite

theorem out_finite_of_relIndex {H : Type} [Group H] (V K : Subgroup H) (hi : V.relIndex K ≠ 0) :
    {q : H ⧸ V | q.out ∈ K}.Finite := by
  have hm : Nat.card (K ⧸ V.subgroupOf K) ≠ 0 := hi
  haveI : Finite (K ⧸ V.subgroupOf K) := Nat.finite_of_card_ne_zero hm
  have hinj : Function.Injective (fun q : {q : H ⧸ V | q.out ∈ K} =>
      (((⟨q.1.out, q.2⟩ : K)) : K ⧸ V.subgroupOf K)) := by
    intro a b hab
    have h1 := QuotientGroup.eq.1 hab
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (a.1.out)⁻¹ * b.1.out ∈ V := by simpa using h1
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' a.1, ← QuotientGroup.out_eq' b.1]
    exact QuotientGroup.eq.2 h2
  haveI : Finite {q : H ⧸ V | q.out ∈ K} := Finite.of_injective _ hinj
  exact Set.toFinite _

theorem hint_prod_eq_foldr : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH V : ∀ i, Subgroup (Hl i))
    (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i ∧ f i = (KH i : Set (Hl i)).indicator 1)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x)
    (l : List ι) (hl : l.Nodup)
    (hfix : ∀ i, i ∉ l → (fun x => hint (KH i) fun m => f i m * g (x * e i m)) = g),
    hint K (fun x => (∏ᶠ i, f i (p i x)) * g x) =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g 1 := by
  intro ι Γ _ Hl _ p e K KH V f hpe hpe' hsep hev hK hVK hVi hVe hfV hfs g hg l hl hfix
  have hmemL : ∀ u, u ∈ (⨅ i, (V i).comap (p i)) ↔ ∀ i, p i u ∈ V i := by
    intro u
    simp [Subgroup.mem_iInf]
  generalize hLdef : (⨅ i, (V i).comap (p i)) = L at hmemL
  have hLK : L ≤ K := fun u hu => (hK u).2 fun i => hVK i ((hmemL u).1 hu i)
  have hfinKH : ∀ i, {q : Hl i ⧸ V i | q.out ∈ KH i}.Finite :=
    fun i => out_finite_of_relIndex (V i) (KH i) (hVi i)
  have hVe1 : ∀ᶠ i in cofinite, V i = KH i := hVe.mono fun i h => h.1
  have hidx : L.relIndex K ≠ 0 := by
    refine relIndex_ne_of_out L K hLK ?_
    have h0 := _root_.GlobalTheory.CompanionTheory.FinActS.finite_cosets_of_components_mem p V (fun i => (KH i : Set (Hl i)))
      (fun i x hx u hu => mul_mem hx (hVK i hu)) hfinKH
      (hVe1.mono fun i h x hx => by
        rw [SetLike.mem_coe, h]
        exact hx)
    rw [hLdef] at h0
    exact h0.subset fun q hq => (hK _).1 hq
  have hB := Filter.eventually_cofinite.1 hVe
  obtain ⟨extra, hextra, hend, hcov⟩ : ∃ extra : List ι, (∀ i ∈ extra, i ∉ l) ∧ extra.Nodup ∧
      ∀ j, j ∉ l ++ extra → V j = KH j ∧ f j = (KH j : Set (Hl j)).indicator 1 := by
    refine ⟨(hB.toFinset.filter (· ∉ l)).toList, ?_, Finset.nodup_toList _, ?_⟩
    · intro i hi
      rw [Finset.mem_toList, Finset.mem_filter] at hi
      exact hi.2
    · intro j hj
      by_contra hc
      apply hj
      rw [List.mem_append]
      by_cases hjl : j ∈ l
      · exact Or.inl hjl
      · refine Or.inr ?_
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨hB.mem_toFinset.2 hc, hjl⟩
  have hnd : (l ++ extra).Nodup :=
    List.Nodup.append hl hend fun a ha hb => hextra a hb ha
  generalize hT : l ++ extra = T at hnd hcov
  have hfoldE : ∀ m : List ι, (∀ i ∈ m, i ∉ l) →
      m.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g = g := by
    intro m
    induction m with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hm
      rw [List.foldr_cons, ih fun i hi => hm i (List.mem_cons_of_mem _ hi)]
      exact hfix a (hm a List.mem_cons_self)
  have hfold : T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g := by
    rw [← hT, List.foldr_append, hfoldE extra hextra]
  have hsum := _root_.GlobalTheory.CompanionTheory.FinActSum.sum_formula p e KH V f hpe hpe' hsep hev hVK hVi hVe1 hfV hfs T hnd g hg 1
  rw [hLdef] at hsum
  simp only [one_mul] at hsum
  have hF : ∀ x, (∏ᶠ j, if j ∈ T then f j (p j x)
      else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) = ∏ᶠ i, f i (p i x) := by
    intro x
    refine finprod_congr fun j => ?_
    split_ifs with hj
    · rfl
    · obtain ⟨h1, h2⟩ := hcov j hj
      rw [h2, h1]
  simp only [hF] at hsum
  have hlev : L ≤ rStab (fun x => (∏ᶠ i, f i (p i x)) * g x) := by
    intro r hr
    refine GlobalTheory.CompanionTheory.FamClP.mem_rStab'.2 fun x => ?_
    have h1 : (∏ᶠ i, f i (p i (x * r))) = ∏ᶠ i, f i (p i x) := by
      refine finprod_congr fun i => ?_
      rw [map_mul]
      exact hfV i _ ((hmemL r).1 hr i) _
    show (∏ᶠ i, f i (p i (x * r))) * g (x * r) = (∏ᶠ i, f i (p i x)) * g x
    rw [h1, hg r ((hmemL r).1 hr) x]
  have h1 := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L (fun x => (∏ᶠ i, f i (p i x)) * g x) hLK hlev hidx

  have hfVI : ∀ i, ∀ u ∈ V i, ∀ x, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) (x * u) =
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) x := by
    intro i u hu x
    have h0 : u ∈ rStab ((KH i : Set (Hl i)).indicator (1 : Hl i → ℂ)) := by
      rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]
      exact hVK i hu
    exact GlobalTheory.CompanionTheory.FamClP.mem_rStab'.1 h0 x
  have hfsI : ∀ i, {q : Hl i ⧸ V i | (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) q.out ≠ 0}.Finite := by
    intro i
    refine (hfinKH i).subset fun q hq => ?_
    by_contra hn
    exact hq (Set.indicator_of_notMem (s := (KH i : Set (Hl i))) (show q.out ∉ (KH i : Set (Hl i)) from hn) _)
  have hsum2 := _root_.GlobalTheory.CompanionTheory.FinActSum.sum_formula p e KH V (fun i => (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ))
    hpe hpe' hsep hev hVK hVi hVe1 hfVI hfsI T hnd (fun _ => 1) (fun _ _ _ => rfl) 1
  rw [hLdef] at hsum2
  have hfold2 : ∀ m : List ι, m.foldr (fun i g' x => hint (KH i) fun m =>
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) m * g' (x * e i m)) (fun _ => (1 : ℂ)) =
      fun _ => 1 := by
    intro m
    induction m with
    | nil => rfl
    | cons a t ih =>
      rw [List.foldr_cons, ih]
      funext x
      simp only [mul_one]
      exact GlobalTheory.CompanionTheory.FamClP.hint_ind _
  rw [hfold2 T] at hsum2
  have hF2 : ∀ x, (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)
      else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) =
      (K : Set Γ).indicator (1 : Γ → ℂ) x := by
    intro x
    have h0 : (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)
        else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) =
        ∏ᶠ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) := by
      refine finprod_congr fun j => ?_
      split_ifs with hj
      · rfl
      · rw [(hcov j hj).1]
    rw [h0]
    by_cases hx : x ∈ K
    · have h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 1 := Set.indicator_of_mem hx _
      rw [h2]
      have h3 : ∀ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) = 1 :=
        fun j => Set.indicator_of_mem ((hK x).1 hx j) _
      simp only [h3, finprod_one]
    · have h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 0 := Set.indicator_of_notMem hx _
      rw [h2]
      have h3 : ∃ j, p j x ∉ KH j := by
        by_contra hc
        push_neg at hc
        exact hx ((hK x).2 hc)
      obtain ⟨j, hj⟩ := h3
      refine finprod_eq_zero _ j (Set.indicator_of_notMem hj _) ?_
      refine (Filter.eventually_cofinite.1 (hev x)).subset fun i hi hin => hi ?_
      exact Set.indicator_of_mem hin _
  simp only [hF2, mul_one] at hsum2
  have h2 := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L ((K : Set Γ).indicator (1 : Γ → ℂ)) hLK
    (by rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]; exact hLK) hidx
  rw [GlobalTheory.CompanionTheory.FamClP.hint_ind, hsum2] at h2
  have hC : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hCeq : (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod = ((L.relIndex K : ℕ) : ℂ) := by
    have h3 : ((L.relIndex K : ℕ) : ℂ) * (((L.relIndex K : ℕ) : ℂ)⁻¹ *
        (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod) = ((L.relIndex K : ℕ) : ℂ) * 1 := by
      rw [← h2]
    rwa [← mul_assoc, mul_inv_cancel₀ hC, one_mul, mul_one] at h3
  rw [h1, hsum, hCeq, ← mul_assoc, inv_mul_cancel₀ hC, one_mul, hfold]

end GlobalTheory.CompanionTheory.FinActCore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_product_word_in_shuffle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSegJacquet k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) → ∀ w : List (IrrGL (k := k)), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w := by
  first | exact @GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | exact GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | (intros; apply GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftUnipotentLeviCommutator
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.ThTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ShEmbUnip


set_option maxHeartbeats 1000000 in
theorem sh_emb_unip : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
    ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
      z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  intro D n ρ p hn M g₁ b hg y
  have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨g₁, hg⟩
  have hE := M.emb_mat g₁ _ _ _ _ hg
  refine ⟨⟨HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y), ?_⟩, HMul.hMul y b, ?_, rfl⟩
  · show adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]
  · apply mat_injective'
    rw [mat_mul' (M.sh y), mat_mul' _ (M.sh y), mat_mul' (M.nzx _ _), M.sh_mat, M.nzx_mat, hE, blockMatrix_zero, blockRowSubstitution_one,
      submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add,
      adj_mul, hb, Matrix.mul_neg, add_neg_cancel]

end GlobalTheory.CompanionTheory.ShEmbUnip

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlaces
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.DxN

theorem selfDual_isEulerProd_n : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → GlobalTheory.CompanionTheory.SW.IsEulerProd b dx 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (fun v => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) ∧ ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM ψ hψ dx hdx d b laminf lam hinf hlam
  exact selfDual_isEulerProd_tuple F E σ hCM M J hJ n hM ψ hψ dx hdx d b laminf lam hinf hlam

end GlobalTheory.CompanionTheory.SiegelND.DxN

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneral
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem data_zero_of_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {ψ} {ι : Type} [Fintype ι] {θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν}
    (h : PositivityTheory.SiegelWeilFormula.Gen.Dat (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν) :
    PositivityTheory.SiegelWeilFormula.Gen.Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν :=
  { cm := h.cm, herm := h.herm, hT := h.hT, det := h.det, chr := h.chr, places := h.places,
    frames := h.frames, haar := h.haar, co := h.co, std := h.std, pure := h.pure, prod := h.prod,
    sdW := h.sdW, sdH := h.sdH }

theorem whitKAOfGenLt : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  intro hGen hDict hAn D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩ := hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν
  have key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j) := by
    intro j
    obtain ⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩ := hm j
    have h := hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (data_zero_of_data hDat) hDat.lt (hAn D n V hR) False.elim
      ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕
    have e : ((V.rank : ℂ) - n) / 2 = s0 V n := by
      simp only [s0]
      ring
    rw [hval ν 𝓕 hS.hν h𝓕]
    rw [one_mul] at h
    have h2 := (holValueAt_const C _).mul h
    rw [e] at h2
    exact h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩
  rw [hv]
  exact (holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩

end GlobalTheory.CompanionTheory.IwaAd

end
end

