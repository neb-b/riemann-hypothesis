module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem tieAdmG_of_record (D : Formalism.BasicNotions.D7) : TieAdmG D :=
  fun k => ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

theorem wg_le_badBound (g m N q : ℝ) (n : ℕ) (r : ℝ) (hg : 2 ≤ g) (hm : 0 ≤ m) (hr : 100 ≤ r) (hrN : r ≤ N) :
    3 * (n : ℝ) / g + 23 * (n : ℝ) * Real.log g / Real.sqrt g +
        2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) + r / 2 * (7 / 8 : ℝ) ^ n +
        Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ badBound g n m N q := by
  unfold badBound
  have hf : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos (by linarith)
  have hlN : Real.log r ≤ Real.log N := Real.log_le_log hr0 hrN
  have hg1 : 0 < g - 1 := by linarith
  have t3 : 2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) ≤
      2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) := by
    have : (1 + Real.log r) / (g - 1) ≤ (1 + Real.log N) / (g - 1) :=
      div_le_div_of_nonneg_right (by linarith) hg1.le
    have h0 : 0 ≤ 2 * (n : ℝ) * m := by positivity
    nlinarith
  have t4 : r / 2 * (7 / 8 : ℝ) ^ n ≤ N / 2 * (7 / 8 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    have : 0 ≤ (7 / 8 : ℝ) ^ n := by positivity
    nlinarith
  have t5 : Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ Real.exp (-((n : ℝ) / (10 * Real.log N))) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hf (by positivity) (by linarith)
  linarith

end GlobalTheory.BadNumOnto

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem badShare_numbers_onto : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  refine ⟨1, one_pos, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨xs, hs⟩ := GlobalTheory.family_eventually_size_bounds eps Fm 5 (by norm_num)
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hezle : Fm.ez ≤ eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.ez_le
    rwa [Fm.L_ez 0 i, Fm.L_eps 0 i] at this
  obtain ⟨xb, hb⟩ := badBound_numbers Fm.ez 5 hez (hezle.trans he1)
  have he7 : 0 < Fm.ez / 7 := by positivity
  obtain ⟨xe, hxe⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop he7).eventually_ge_atTop (4 : ℝ)).and
      (((tendsto_rpow_atTop he).eventually_ge_atTop (512 : ℝ)).and (Filter.eventually_ge_atTop (1 : ℝ))))
  refine ⟨max (max xs xb) xe, fun x hx1 hx ι => ?_⟩
  have hxs : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxb : xb ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  obtain ⟨h7, h512, hx1'⟩ := hxe x ((le_max_right _ _).trans hx)
  rw [Fm.L_x x ι hx1, Fm.L_ez x ι]
  have hE : Real.exp (-(x ^ (Fm.ez / 7))) ≤ 1 / 4 := by
    have h1 : (4 : ℝ) ≤ Real.exp (x ^ (Fm.ez / 7)) := by
      have := Real.add_one_le_exp (x ^ (Fm.ez / 7)); linarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h1
  have hr100 : 100 ≤ (Fm.D x ι).R.r := (hs x hxs ι 0).2.2.2.2.1
  refine ⟨hr100, tieAdmG_of_record _, hE, fun k => ?_⟩
  obtain ⟨hg, hf2, hf5, hm5, -, hr5, hq⟩ := hs x hxs ι k
  have hg12 : (2 : ℝ) ^ 12 ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans ?_ hg
    have := Real.add_one_le_exp (8 * x ^ eps)
    norm_num
    linarith
  refine ⟨by exact_mod_cast hg12, ?_⟩
  have hr100' : (100 : ℝ) ≤ ((Fm.D x ι).R.r : ℝ) := by exact_mod_cast hr100
  have hepsC : x ^ Fm.ez ≤ x ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hgz : Real.exp (8 * x ^ Fm.ez) ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans (Real.exp_le_exp.2 ?_) hg
    have := Real.rpow_le_rpow_of_exponent_le hx1' hezle
    linarith
  obtain ⟨-, hbb0, hbb⟩ := hb x hxb ((Fm.D x ι).host.g k) ((Fm.D x ι).R.f) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) hgz
    (by rw [Real.rpow_two]; exact hf2) hf5 (Nat.cast_nonneg _) hm5 (le_max_right _ _) (max_le hr5 hepsC) hq
  have hW := wg_le_badBound ((Fm.D x ι).host.g k) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) ((Fm.D x ι).R.f)
    ((Fm.D x ι).R.r) (by linarith) (Nat.cast_nonneg _) hr100' (le_max_left _ _)
  linarith

end GlobalTheory.BadNumOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistence
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem li_one_tmul_of_li {O K' M : Type} [CommRing O] [IsDomain O] [Field K'] [Algebra O K']
    (hO : Function.Injective (algebraMap O K'))
    [AddCommGroup M] [Module (FractionRing O) M] [Module O M] [IsScalarTower O (FractionRing O) M] {n : ℕ} (m : Fin n → M)
    (hm : LinearIndependent (FractionRing O) m) :
    LinearIndependent K' fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination (FractionRing O) m).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hm.fintypeLinearCombination_injective)
  have hgm : ∀ a, g (m a) = Pi.single a 1 := fun a => by
    have h := LinearMap.congr_fun hg (Pi.single a 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Fintype.linearCombination_apply_single, one_smul] at h
    exact h
  let κ : FractionRing O →ₐ[O] K' := IsFractionRing.liftAlgHom (K := FractionRing O) (g := Algebra.ofId O K') hO
  let φ : M →ₗ[O] (Fin n → K') := LinearMap.pi fun k =>
    κ.toLinearMap.comp ((LinearMap.proj k).comp (g.restrictScalars O))
  let F := φ.liftBaseChange K'
  have hF : ∀ a, F ((1 : K') ⊗ₜ[O] m a) = Pi.single a 1 := fun a => by
    simp only [F, LinearMap.liftBaseChange_tmul, one_smul]
    funext k
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.proj_apply, hgm,
      AlgHom.toLinearMap_apply]
    by_cases h : k = a
    · subst h; simp
    · simp [Pi.single_apply, h]
  refine LinearIndependent.of_comp F ?_
  have : (F ∘ fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M)) = fun a => Pi.single a (1 : K') := funext hF
  rw [this]
  convert (Pi.basisFun K' (Fin n)).linearIndependent using 1
  funext a
  exact (Pi.basisFun_apply K' (Fin n) a).symm

theorem embW_tmul_eq {D : D7} (S : NX.RatDat D.ntw) (c : NChoice D) (hc : NChTie D c) (w : D.what₂.places.Pl) {M : Type}
    [AddCommGroup M] [Module (FractionRing (D.ntw.O (c.twI w))) M] [Module (D.ntw.O (c.twI w)) M]
    [IsScalarTower (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) M] (a : S.Ks) (m : M) :
    (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
        ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) := by
  classical
  set e0 := (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) (S.kKs a) with he0
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) e0
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz' : algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have hE : e0 * algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz']
  have h1 := hc.embedding_baseField_condition w (S.kKs a) y z hz0 hE
  rw [S.kKs_spec] at h1
  set zO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z with hzO
  set yO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y with hyO
  have hφ : ∀ u : D.ntw.O (c.twI w), algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) u =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) u)) := fun u => by
    rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w)),
      IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  have hι : (show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) *
      algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) zO = algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) yO := by
    have hm : ∀ u : D.ntw.O0 (c.twI w), IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w)))
        (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w)) (algebraMap _ _ u) = algebraMap (D.ntw.O (c.twI w)) _ (algebraMap _ _ u) :=
      fun u => IsLocalization.map_eq _ _
    change (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w)))
        (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) e0 * _ = _
    rw [hzO, hyO, ← hm, ← hm, ← map_mul, hE]
  have hζ : algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO ≠ 0 := by
    rw [hφ]
    intro h0
    apply hz0
    have := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (h0.trans (map_zero _).symm)
    have := c.Oe_inj w (this.trans (map_zero _).symm)
    have := D.ntw.Ok_inj (c.twI w) (c.k' w) (this.trans (map_zero _).symm)
    exact D.ntw.O_inj (c.twI w) (this.trans (map_zero _).symm)
  have key : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M,
      zO • t = algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO • t :=
    fun t => (algebraMap_smul (FractionRing (c.Oe w)) zO t).symm
  have hL : zO • (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, hφ, mul_comm, h1, ← hφ, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have hR : zO • ((1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
      ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m) := by
    rw [← TensorProduct.tmul_smul]
    congr 1
    rw [← algebraMap_smul (FractionRing (D.ntw.O (c.twI w))) zO, smul_smul, mul_comm, hι, algebraMap_smul]
  have h2 := (key _).symm.trans (hL.trans (hR.symm.trans (key _)))
  exact smul_right_injective _ hζ h2

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem canEx_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    ∃ rd : Can p w j, IsCan p rd ∧ ∃ (n : ℕ) (β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL)),
      LinearIndependent (FractionRing (ex.nch.Oe w)) fun a => rd (β a) := by
  classical
  obtain ⟨n, b, hbK, hliK, hspK, hliL, hspL⟩ := p.fw.ks j
  have hEs : ∀ (a : p.Sx.Ks) (v : p.Sx.WL ((j : ℕ) + 1)), (p.nexp.fi j).e (a • v) = (p.nexp.fi j).eK a • (p.nexp.fi j).e v :=
    fun a v => by
      rw [← algebraMap_smul D.what₂.LL a v, LinearEquiv.map_smul, ← (p.nexp.fi j).eK_LL, algebraMap_smul]
  let f : Fin n → NX.FmK p.Sx ((j : ℕ) + 1) := fun k =>
    ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hbK k)⟩
  have hf : ∀ k, (p.nexp.fi j).e (f k).1 = b k := fun k => LinearEquiv.apply_symm_apply _ _
  let v : NX.FmK p.Sx ((j : ℕ) + 1) →ₗ[p.Sx.Ks] p.Sx.WL ((j : ℕ) + 1) := (p.Sx.A ((j : ℕ) + 1)).WK.subtype
  have hv : ∀ g, v g = g.1 := fun _ => rfl
  have hsum : ∀ a : Fin n → p.Sx.Ks, (p.nexp.fi j).e (∑ k, a k • f k).1 = ∑ k, (p.nexp.fi j).eK (a k) • b k := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hv, hEs, hf]
  have hdec : ∀ g : NX.FmK p.Sx ((j : ℕ) + 1), ∃ a : Fin n → p.Sx.Ks, g = ∑ k, a k • f k := by
    intro g
    have hg : (p.nexp.fi j).e g.1 ∈ (p.R.FW j).WK := ((p.nexp.fi j).wk _).1 g.2
    rw [← hspK, Submodule.mem_span_range_iff_exists_fun] at hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨fun k => (p.nexp.fi j).eK.symm (c k), Subtype.ext ((p.nexp.fi j).e.injective ?_)⟩
    rw [hsum, ← hc]
    simp only [RingEquiv.apply_symm_apply]
  have hliF : LinearIndependent p.Sx.Ks f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h0 : ∑ k, (p.nexp.fi j).eK (a k) • b k = 0 := by
      rw [← hsum, ha, ← hv, map_zero, map_zero]
    have := (Fintype.linearIndependent_iff.1 hliK) _ h0 k
    exact (map_eq_zero_iff _ (p.nexp.fi j).eK.injective).1 this
  let bK : Module.Basis (Fin n) p.Sx.Ks (NX.FmK p.Sx ((j : ℕ) + 1)) := Module.Basis.mk hliF (fun g _ => by
    obtain ⟨a, rfl⟩ := hdec g
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  set eF := p.nexp.eF (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (Nat.le_add_left _ _) j.2 with heF
  let m : Fin n → D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) := fun k =>
    eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k)
  let t : Fin n → Tgt ex w j := fun k => (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m k
  let β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL) := Module.Basis.mk hliL hspL.ge
  have hβ : ∀ k, β k = b k := fun k => Module.Basis.mk_apply _ _ _
  let rd : Can p w j :=
    { toFun := fun x => ∑ k, ex.nch.embW w (β.equivFun x k) • t k
      map_add' := fun x y => by simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  have hrd : ∀ x, rd x = ∑ k, ex.nch.embW w (β.equivFun x k) • t k := fun _ => rfl
  refine ⟨rd, fun g => ?_, n, β, ?_⟩
  · obtain ⟨a, rfl⟩ := hdec g
    have hx : (p.nexp.fi j).e (∑ k, a k • f k).1 = β.equivFun.symm fun k => algebraMap p.Sx.Ks D.what₂.LL (a k) := by
      rw [hsum, Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ, ← (p.nexp.fi j).eK_LL]
      exact (algebraMap_smul D.what₂.LL _ _).symm
    have hterm : ∀ k, ex.nch.embW w (algebraMap p.Sx.Ks D.what₂.LL (a k)) • t k =
        (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] (a k • f k)) := fun k => by
      simp only [t, m]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, embW_tmul_eq p.Sx ex.nch ex.nch_tie w]
      congr 1
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) (a k)]
      exact (eF.symm.map_smul _ _).symm
    refine (hrd _).trans ?_
    rw [hx, LinearEquiv.apply_symm_apply, Finset.sum_congr rfl fun k _ => hterm k, ← TensorProduct.tmul_sum]
    congr 1
    rw [TensorProduct.tmul_sum]
    exact (map_sum eF.symm _ _).symm
  · have hB : LinearIndependent (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) fun k =>
        ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k :
          NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w) ⊗[p.Sx.Ks] NX.FmK p.Sx ((j : ℕ) + 1)) := by
      have := (Algebra.TensorProduct.basis (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) bK).linearIndependent
      convert this using 1
      funext k
      rw [Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
    let u : Fin n → NX.Fm p.Sx (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) := fun k =>
      (1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k
    have hB' : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) u := hB
    have hm : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) m := hB'.map' eF.symm.toLinearMap eF.symm.ker
    have hO : Function.Injective (algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w))) := by
      have e1 : algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w)) =
          (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))).comp
            ((algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w)).comp
              (algebraMap (D.ntw.O (ex.nch.twI w)) (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)))) := by
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      rw [e1, RingHom.coe_comp, RingHom.coe_comp]
      exact (IsFractionRing.injective _ _).comp ((ex.nch.Oe_inj w).comp (D.ntw.Ok_inj _ _))
    have hrb : ∀ a, rd (β a) = t a := fun a => by
      rw [hrd, Finset.sum_eq_single a]
      · simp [Module.Basis.equivFun_self]
      · intro k _ hk
        simp [Module.Basis.equivFun_self, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ a) h
    have := li_one_tmul_of_li (K' := FractionRing (ex.nch.Oe w)) hO m hm
    have ht : (fun a => rd (β a)) = t := funext hrb
    rw [ht]
    exact this

end Point

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

namespace GlobalTheory.BigOn.Exp.ProjRd

attribute [local instance] GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.algKK


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem rd_eOp {D : D7} {c : NChoice D} {w : D.what₂.places.Pl} (ht : NChTie D c) {Gp : Type} [Group Gp] [Fintype Gp]
    (I : Gp ≃* G0g D.nd) (S : RatDat D.ntw) (j : ℕ)
    {Ks' WL' : Type} {_ : Field Ks'} {_ : NumberField Ks'} {_ : Algebra Ks' D.what₂.LL} {_ : AddCommGroup WL'}
    {_ : Module D.what₂.LL WL'} {_ : Module Ks' WL'} [IsScalarTower Ks' D.what₂.LL WL']
    {_ : Module (𝓞 Ks') WL'} {_ : IsScalarTower (𝓞 Ks') Ks' WL'}
    {W' : (D.what₂.LL →+* ℂ) → Type} {_ : ∀ σ, NormedAddCommGroup (W' σ)} {_ : ∀ σ, InnerProductSpace ℂ (W' σ)}
    (A' : FormsL D.what₂.LL Ks' WL' W' Gp) (fi : FormsIso (S.A j) A') (hks : (S.A j).IsKsForm)
    (hgeq : ∀ s, I (fi.eG s) = S.eG s)
    (rho : RhoStab S j) (chi : ChiInLL0 S j)
    (eF : D.nexp.Fm (c.twI w) j (c.sd w) ≃ₗ[FractionRing (D.ntw.O (c.twI w))] Fm S (c.twI w) j (c.sd w))
    (hact : ∀ g x, eF (D.nexp.actG (c.twI w) j (c.sd w) g x) = actG S (c.twI w) j (c.sd w) rho chi g (eF x))
    (eC : Gp → D.what₂.LL) (heC : ∀ h, eC h = (D.nexp.eLL0 (I h) : D.what₂.LL))
    (rd : WL' →ₛₗ[c.embW w] FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w))
    (hrd : ∀ f : FmK S j, rd (fi.e (Subtype.val f)) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] eF.symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f))
    (y : WL') :
    rd (A'.eOp eC y) = GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) (rd y) := by
  classical
  obtain ⟨e, -, -, h3, h4⟩ := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.stage1 (w := w) ht j S hks rho chi eF hact
  have hre : ∀ x, rd (fi.e x) = e x := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hks
    have hx : x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    have h5 := h3 n a (fun k => ⟨b k, hbK k⟩)
    refine Eq.trans ?_ h5.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    rw [hrd ⟨b k, hbK k⟩, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨x, rfl⟩ := fi.e.surjective y
  letI : Fintype S.G := Fintype.ofEquiv Gp fi.eG.symm.toEquiv
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Gp I.toEquiv
  have hL : A'.eOp eC (fi.e x) = fi.e (∑ s : S.G, eC (fi.eG s) •
      ((((S.A j).chi s)⁻¹ : D.what₂.LLˣ).val • (S.A j).ρ s x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, FormsL.eOp, LinearMap.sum_apply]
    refine (Fintype.sum_equiv fi.eG.toEquiv _ _ fun s => ?_).symm
    rw [map_smul, map_smul, fi.rho]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, LinearMap.smul_apply, smul_smul, fi.chi]
  have hR : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w),
      GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) t = ∑ s : S.G,
        algebraMap (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w)) ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s)) •
          GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.ext (D.ntw.O (c.twI w)) (FractionRing (c.Oe w))
            ((D.nexp.actG (c.twI w) j (c.sd w) (S.eG s)).toLinearMap) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [map_add (f := _), hu, hv, ← Finset.sum_add_distrib]; simp only [map_add (f := _), smul_add]
    | tmul a m =>
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) (a ⊗ₜ m) =
          a ⊗ₜ[D.ntw.O (c.twI w)] GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp D.nexp (c.twI w) j (c.sd w) m := rfl
      have h2 : GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp D.nexp (c.twI w) j (c.sd w) m = ∑ s : S.G,
          (D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s) • D.nexp.actG (c.twI w) j (c.sd w) (S.eG s) m := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp
        rw [GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lift_eq_sum, LinearMap.sum_apply]
        exact (Fintype.sum_equiv S.eG.toEquiv _ _ fun s => rfl).symm
      rw [h1, h2, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.tmul_smul_frac, GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.ext_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, hre, hre, hR, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smulₛₗ, h4 s x]
  congr 1
  rw [heC, hgeq, GlobalTheory.Proof.FractionFieldEmbeddingCompat.embW_eq_of_tie ht w]
  change _ = fracExt c w ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s))
  rw [D.nexp.eAlg_def]
  rfl

end GlobalTheory.BigOn.Exp.ProjRd

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadicalStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∃ φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × GlobalTheory.ResidueEisenstein.ModConj.skewA σ j → GAd σ J, Continuous φ ∧ ∀ b s, GlobalTheory.SphEis.Crd σ J C D Z J₀ (φ (b, s)) b ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * GlobalTheory.SphEis.plus σ J₀ b)) := by
  first | exact @GlobalTheory.ResidueEisenstein.ChartU.chart | exact GlobalTheory.ResidueEisenstein.ChartU.chart | (intros; apply GlobalTheory.ResidueEisenstein.ChartU.chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelOppositeLagrangianUnitaryOpStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_vac_eq_of_localVacuum_linearModel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s m : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      GlobalTheory.Hk3.LocVac ρ m → ∃ c : ℂ, m = c • s := by
  first | exact @GlobalTheory.InertBridgeLine.locVac_line | exact GlobalTheory.InertBridgeLine.locVac_line | (intros; apply GlobalTheory.InertBridgeLine.locVac_line <;> assumption)
end

