module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinitePointsCarryLatticeVacuumToMovedVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem ipO_Th_self_eq (D : D7) (S T : HSp D) (C : Ctx S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (hμ : IsCovolOne (ratL T S) μ 𝓕) (x : Frame C.X.Ψ T.rank) (hx : x ∈ C.X.dom)
    (v v' : TF S.rank C.g) (hv : SW.IsSB v) (hv' : SW.IsSB v') (h : SW.ip v v = SW.ip v' v') :
    ipO μ 𝓕 (C.Th x v) (C.Th x v) = ipO μ 𝓕 (C.Th x v') (C.Th x v') := by

  have hR : IsRealPt (0 : WO S T) := by simp [IsRealPt]
  obtain ⟨a, -, b, -, hab⟩ :=
    GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
  have hip := (ScalarProduct.ip_basic D S T C).2 μ 𝓕 hμ
  have key : ∀ φ : TF S.rank C.g, SW.IsSB φ → ipO μ 𝓕 (C.Th x φ) (C.Th x φ) =
      a * SW.ip φ φ * (gaussR C.X C.bas C.idx x (C.zOf x 0) * conj (gaussR C.X C.bas C.idx x (C.zOf x 0)) *
        kZero C.X C.idx x x (C.zOf x 0) (fun k i => conj (C.zOf x 0 k i))) := by
    intro φ hφ
    have hT : C.IsTh (C.Th x φ) := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C x hx φ hφ).1.1
    rw [← ((hip _ hT).2.2.2 _ hT).2.2.2.2.1 0,
      _root_.GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ x hx x hx φ φ hφ hφ 0 0 hR hR, (hab φ φ hφ hφ).1]
  rw [key v hv, key v' hv', h]

theorem om_Th_vac : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ Λ' ∈ Vset D.host.E S.rank M, ∀ L L' : Lt D.host.E T.rank, SelfD C.X L → SelfD C.X L' → ∀ h ∈ GfC S, ∀ g ∈ GfC T, IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → ∀ v v', IsVac C.X C.bas w (tens Λ L) v → IsVac C.X C.bas w (tens Λ' L') v' → ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ om (h, g) (C.Th (C.xB B) v) = c • (C.Th (C.xB B) v') := by
  intro D S T C om hom w hwi hw1 hw2 M Λ hΛ Λ' hΛ' L L' hL hL' h hh g hg hmS hmT v v' hv hv' B hB
  have hBB := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hx : C.xB B ∈ C.X.dom := hBB.2.1
  have hfix : C.mvB g B = B := (hBB.2.2.2.2.2 g).2.2.1 hg
  set f := C.Th (C.xB B) v with hf
  set f' := C.Th (C.xB B) v' with hf'
  have hfT : C.IsTh f := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx v hv.1).1.1
  have hfT' : C.IsTh f' := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx v' hv'.1).1.1

  have hLat : IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f :=
    ((_root_.GlobalTheory.Ker.latVac_th_line D S T C w hwi hw1 hw2 M Λ hΛ L hL).1 _ hx v hv.1).2 hv.2.2
  have hLat' : IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) :=
    (_root_.GlobalTheory.TensLatMove.hatA_move D S T C h g Λ Λ' L L' hmS hmT).2 om hom f hfT hLat
  have hTh : C.IsTh (om (h, g) f) := hom.om_pres (h, g) f hfT
  have hFock : C.IsFock B (om (h, g) f) := by
    have h1 := ((_root_.GlobalTheory.Ker.WeakMove.om_move D S T C om hom h g f hfT).2 B hB).1
      ((_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB v hv.1).1
    rwa [hfix] at h1
  obtain ⟨t, ht⟩ :=
    (_root_.GlobalTheory.Ker.latVac_th_line D S T C w hwi hw1 hw2 M Λ' hΛ' L' hL').2 B hB v' hv' _ hTh hFock hLat'

  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := ScalarProduct.ip_basic D S T C
  have hsame : ipO μ 𝓕 f f = ipO μ 𝓕 f' f' :=
    ipO_Th_self_eq D S T C μ 𝓕 hμ _ hx v v' hv.1 hv'.1 (by rw [hv.2.1, hv'.2.1])
  have hom_eq : ipO μ 𝓕 (om (h, g) f) (om (h, g) f) = ipO μ 𝓕 f f :=
    ((hip μ 𝓕 hμ f hfT).2.2.2 f hfT).2.2.2.2.2 om hom (h, g)
  have hsc : ipO μ 𝓕 (t • f') (t • f') = t * conj t * ipO μ 𝓕 f' f' := by
    simp only [ipO, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  by_cases h0 : ipO μ 𝓕 f' f' = 0
  · have hz' : f' = 0 := (hip μ 𝓕 hμ f' hfT').2.1 h0
    have hz : f = 0 := (hip μ 𝓕 hμ f hfT).2.1 (hsame.trans h0)
    refine ⟨1, by simp, ?_⟩
    rw [hz, hz', map_zero, smul_zero]
  · refine ⟨t, ?_, ht⟩
    have h2 : t * conj t = 1 := by
      have := hom_eq
      rw [ht, hsc, hsame] at this
      exact (mul_left_eq_self₀.mp this).resolve_right h0
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖t‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖t‖ := norm_nonneg t
    nlinarith [sq_nonneg (‖t‖ - 1), sq_nonneg (‖t‖ + 1)]

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevVec

variable {D : D7} {S T : HSp D}

theorem th_sum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type} (s : Finset ι)
    (f : ι → TF S.rank C.g) (hf : ∀ i, SW.IsSB (f i)) :
    C.Th x (∑ i ∈ s, f i) = ∑ i ∈ s, C.Th x (f i) := by
  classical
  have h0 : C.Th x 0 = 0 := by
    simpa using (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 SW.isSB_zero).2.1 0
  refine Finset.induction_on s (by simpa using h0) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  exact ((_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx (f i) (hf i)).1 _ (GlobalTheory.SW.RecSum.isSB_sum s f hf)).1

theorem th_finsum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type}
    (f : ι → TF S.rank C.g) (hf : ∀ i, SW.IsSB (f i)) (hfin : (Function.support f).Finite) :
    C.Th x (∑ᶠ i, f i) = ∑ᶠ i, C.Th x (f i) := by
  classical
  have h0 : C.Th x 0 = 0 := by
    simpa using (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 SW.isSB_zero).2.1 0
  have hsub : (Function.support fun i => C.Th x (f i)) ⊆ (hfin.toFinset : Set ι) := by
    intro i hi
    rw [hfin.coe_toFinset, Function.mem_support]
    intro hfi
    exact (Function.mem_support.1 hi) (by simp [hfi, h0])
  rw [finsum_eq_sum_of_support_subset f (by rw [hfin.coe_toFinset]),
    finsum_eq_sum_of_support_subset _ hsub]
  exact th_sum C hx hfin.toFinset f hf

theorem finsum_out_neg {G N : Type} [AddCommGroup G] [AddCommMonoid N] (A B : AddSubgroup G)
    (F : G → N) (hF : ∀ y ∈ A, ∀ δ ∈ B, F (y + δ) = F y) :
    ∑ᶠ c : A ⧸ B.addSubgroupOf A, F (-(c.out : G)) = ∑ᶠ c : A ⧸ B.addSubgroupOf A, F (c.out : G) := by
  classical
  have key : ∀ c : A ⧸ B.addSubgroupOf A, F (-(c.out : G)) = F (((-c).out : A) : G) := by
    intro c
    have hc : ((-c.out : A) : A ⧸ B.addSubgroupOf A) = (((-c).out : A) : A ⧸ B.addSubgroupOf A) := by
      rw [QuotientAddGroup.mk_neg, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hc
    have e : (((-c).out : A) : G) = -(c.out : G) + ((-(-c.out) + (-c).out : A) : G) := by
      push_cast
      abel
    rw [e, hF _ (neg_mem c.out.2) _ hc]
  rw [finsum_congr key]
  exact finsum_comp_equiv (Equiv.neg _) (f := fun c : A ⧸ B.addSubgroupOf A => F ((c.out : A) : G))

private theorem ctx_Th_finsum_of_isSB (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type}
    (f : ι → TF S.rank C.g) (hf : ∀ i, SW.IsSB (f i)) :
    C.Th x (∑ᶠ i, f i) = ∑ᶠ i, C.Th x (f i) := by
  by_cases hfin : (Function.support f).Finite
  · exact th_finsum C hx f hf hfin
  · have h0 : C.Th x 0 = 0 := by
      simpa using (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 SW.isSB_zero).2.1 0
    have hsupp : (Function.support fun i => C.Th x (f i)) = Function.support f := by
      ext i
      simp only [Function.mem_support, ne_eq]
      constructor
      · intro h hfi
        exact h (by rw [hfi, h0])
      · intro h hT
        exact h (((_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx (f i) (hf i)).1 0 SW.isSB_zero).2 (by rw [hT, h0]))
    have hinf : (Function.support fun i => C.Th x (f i)).Infinite := by
      rw [hsupp]
      exact hfin
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hinf, h0]

theorem uVec_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → (∀ f', C.IsBase Lv B f' → ∀ v, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) v → ∃ t : ℂ, t ≠ 0 ∧ f' = t • (C.Th (C.xB B) v)) ∧ ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → C.IsBase Lv B (C.Th (C.xB B) (v₀ C.X.Λ)) ∧ ∀ t : ℂ, C.uVec Lv hn (t • (C.Th (C.xB B) (v₀ C.X.Λ))) = t • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) := by
  intro D S T C Lv hn M hw2 hM0 hM B hB
  classical
  have hs := C.sympl
  have he := C.even
  have h6833 := _root_.GlobalTheory.SW.level_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank hs he Lv hn
  have hΛlats : C.X.Λ ∈ Lv.lats := h6833.1
  have hΛself : SelfD C.X C.X.Λ := hΛlats.1
  have hSelf : SelfD C.X (Lv.sh C.X.Λ) := (h6833.2.2.2.1 _ hΛlats).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := GlobalTheory.SW.Base.stdL_mem_Vset _ _
  have h26522 := _root_.GlobalTheory.Ker.latVac_th_line D S T C Lv.w Lv.w_int Lv.w_tr hw2 M _ hstd _ hSelf
  have hxdom : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  refine ⟨?_, ?_⟩
  · intro f' hf' v hv
    obtain ⟨t, ht⟩ := h26522.2 B hB v hv f' hf'.th hf'.fock hf'.lat
    refine ⟨t, ?_, ht⟩
    rintro rfl
    exact hf'.ne (by simpa using ht)
  · intro v₀ hv₀
    have hv := hv₀ _ hΛlats
    have hvSB : SW.IsSB (v₀ C.X.Λ) := hv.1
    have hvip : SW.ip (v₀ C.X.Λ) (v₀ C.X.Λ) = 1 := hv.2.1
    have hTh := _root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hxdom (v₀ C.X.Λ) hvSB
    have h0 : C.Th (C.xB B) 0 = 0 := by
      simpa using (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hxdom 0 SW.isSB_zero).2.1 0
    refine ⟨⟨(_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hxdom _ hvSB).1.1, ?_,
      ((_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB _ hvSB).1, (h26522.1 _ hxdom _ hvSB).2 hv.2.2⟩, ?_⟩
    · intro hz
      have h1 : C.Th (C.xB B) (v₀ C.X.Λ) = C.Th (C.xB B) 0 := by rw [hz, h0]
      have h2 := (hTh.1 0 SW.isSB_zero).2 h1
      have h3 := GlobalTheory.SW.TensVac.ip_smul_left (φ := (0 : TF S.rank C.g)) (ψ := 0) (0 : ℂ)
        SW.isSB_zero SW.isSB_zero
      rw [h2] at hvip
      simp only [smul_zero, zero_mul] at h3
      rw [h3] at hvip
      exact zero_ne_one hvip
    · intro t
      have htv : SW.IsSB (t • v₀ C.X.Λ) := GlobalTheory.SW.TensVac.sb_smul t hvSB
      have hsbH : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
          SW.IsSB (heisG C.X C.bas y (v₀ C.X.Λ)) :=
        fun y => (GlobalTheory.SW.TensVac.laws C.idx hs he y hvSB).1
      have hterm : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
          Lv.dat hn y • C.Th (C.xB B) (heisG C.X C.bas y (t • v₀ C.X.Λ)) =
            t • C.Th (C.xB B) (Lv.dat hn y • heisG C.X C.bas y (v₀ C.X.Λ)) := by
        intro y
        have e1 := (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hxdom _ (hsbH y)).2.1
        rw [GlobalTheory.SW.TensVac.heisG_smul, e1, e1, smul_comm]
      have hu : unitv (projA C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) (v₀ C.X.Λ)) =
          v₀ C.X.Λ := by
        rw [(GlobalTheory.SW.RecSum.unitv_proj C.idx hs he hstd hSelf hv hv).2, hvip]
        simp
      have hrho : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
          C.rho (finW S T y) (t • C.Th (C.xB B) (v₀ C.X.Λ)) =
            C.Th (C.xB B) (heisG C.X C.bas (-y) (t • v₀ C.X.Λ)) := by
        intro y
        rw [← hTh.2.1 t]
        exact (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hxdom _ htv).2.2.1 y
      simp only [GlobalTheory.Ker.Ctx.uVec, GlobalTheory.SW.Level.phi, hu, hrho]
      refine Eq.trans (finsum_out_neg
        (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ))
        (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ))
        (fun y => Lv.dat hn y • C.Th (C.xB B) (heisG C.X C.bas y (t • v₀ C.X.Λ))) ?_) ?_
      · intro y hy δ hδ
        have hcong : ∀ k, Cong C.X Lv.𝔪 ((y + δ) k) (y k) :=
          GlobalTheory.SW.RecSum.cong_of_mem hstd hM (GlobalTheory.SW.RecSum.near_of_mem hΛlats) (by simpa using hδ)
        have hdat : Lv.dat hn (y + δ) = Lv.dat hn y := h6833.2.2.2.2.2.1 _ _ hcong
        show Lv.dat hn (y + δ) • _ = Lv.dat hn y • _
        rw [hdat, GlobalTheory.SW.TensVac.heisG_smul, GlobalTheory.SW.TensVac.heisG_smul,
          GlobalTheory.SW.RecSum.heis_add C.idx hs he Lv hstd hΛself hSelf hv hy hδ]
      · rw [ctx_Th_finsum_of_isSB C hxdom _ (fun c => GlobalTheory.SW.TensVac.sb_smul _ (hsbH _)), smul_finsum]
        exact finsum_congr fun c => hterm _

end GlobalTheory.Ker.LevVec
end

