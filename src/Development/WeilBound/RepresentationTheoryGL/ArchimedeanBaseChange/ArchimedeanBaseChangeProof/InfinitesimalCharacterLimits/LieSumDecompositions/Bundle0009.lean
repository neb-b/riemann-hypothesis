module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapD
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.InfTree
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapE
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Eig {a : ℕ} (L : Submodule ℂ (Sm E a)) (σ : (E →+* ℂ) → Multiset ℂ) (sh : ℂ) : Submodule ℂ (Sm E a) where
  carrier := {φ | φ ∈ L ∧ ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨L.add_mem hφ.1 hψ.1, fun τ w => by rw [map_add (f := _), hφ.2, hψ.2, smul_add]⟩
  zero_mem' := ⟨L.zero_mem, fun τ w => by rw [map_zero, smul_zero]⟩
  smul_mem' := fun c φ hφ => ⟨L.smul_mem c hφ.1, fun τ w => by rw [map_smul, hφ.2, smul_comm]⟩

def adm (mm : (E →+* ℂ) → Multiset ℂ) (n : ℕ) : Finset ((E →+* ℂ) → Multiset ℂ) := by
  classical
  exact Fintype.piFinset fun τ => ((mm τ).powerset.filter fun σ => Multiset.card σ = n).toFinset

theorem mem_adm {mm : (E →+* ℂ) → Multiset ℂ} {n : ℕ} {σ : (E →+* ℂ) → Multiset ℂ} :
    σ ∈ adm mm n ↔ ∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = n := by
  classical
  unfold adm
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun τ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter, Multiset.mem_powerset]

variable {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem LS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E r, ∀ φ ∈ LS U T, z φ ∈ LS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.LS_stable hU hT (.lie X)) hz φ hφ

theorem RS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E s, ∀ φ ∈ RS U T, z φ ∈ RS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.RS_stable hU hT (.lie X)) hz φ hφ

theorem data_one (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    (∀ τ u, cap τ u (T ψ) = ((mm τ).map (u + ·)).prod • T ψ) ∧
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ LS U T) ∧ (∀ i, q i ∈ RS U T) ∧
      ∀ p, (T ψ).1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  refine ⟨fun τ u => ?_, ?_⟩
  · have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ
    rw [← (BlockSlices.zalg_comm hI T hT.equiv (cap_mem_Zalg τ u) ψ hψ).2, (hinf τ).2 u ψ hψ, map_smul]
  · obtain ⟨n, b, q, hb, hq, he⟩ := BlockSlices.expand hU hT ψ hψ 1 1
    refine ⟨n, b, q, fun i => ?_, fun i => rsF_sub_RS hψ 1 1 (hq i), fun p => ?_⟩
    · exact (Submodule.span_le.2 (lsF_sub_LS hψ 1 1)) (hb i)
    · rw [← he p, BlockSlices.yp_one, mul_one]

theorem LS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    LS U T ≤ ⨆ σ ∈ adm mm r, Eig (LS U T) σ ((s : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le b hb (LS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.1 m₂
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₁ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₁
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : σ.1 ∈ adm mm r := mem_adm.2 (hS σ.1 σ.2).1
  exact Submodule.mem_iSup_of_mem σ.1 (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), hθe σ.1 σ.2⟩)

theorem RS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    RS U T ≤ ⨆ ρ ∈ adm mm s, Eig (RS U T) ρ (-(r : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le q hq (RS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.2 m₁
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₂ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₂
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : (fun τ => mm τ - σ.1 τ) ∈ adm mm s := mem_adm.2 fun τ => by
    refine ⟨Multiset.sub_le_self _ _, ?_⟩
    rw [Multiset.card_sub ((hS σ.1 σ.2).1 τ).1, (hinf τ).1, ((hS σ.1 σ.2).1 τ).2]
    omega
  refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), fun τ w => ?_⟩)
  rw [hθe σ.1 σ.2 τ w]
  congr 3
  funext z
  ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def lowL (X : Lie E (r + s)) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E) :=
  Matrix.of fun i j => if r ≤ (i : ℕ) ∧ (j : ℕ) < r then X i j else 0

def skw (X : Lie E (r + s)) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E) := lowL X - (lowL X)ᴴ

theorem skw_skew (X : Lie E (r + s)) : (skw X)ᴴ = -skw X := by
  rw [skw, conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]

theorem par_low (X : Lie E (r + s)) (i : Fin s) (j : Fin r) :
    (X - toL (skw X)) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  have h1 : lowL X (Fin.natAdd r i) (Fin.castAdd s j) = X (Fin.natAdd r i) (Fin.castAdd s j) := by
    simp [lowL]
  have h2 : lowL X (Fin.castAdd s j) (Fin.natAdd r i) = 0 := by
    simp [lowL]
  change X (Fin.natAdd r i) (Fin.castAdd s j) - (lowL X (Fin.natAdd r i) (Fin.castAdd s j) -
    star (lowL X (Fin.castAdd s j) (Fin.natAdd r i))) = 0
  rw [h1, h2, star_zero, sub_zero, sub_self]

theorem lie_split (X : Lie E (r + s)) (F : Sm E (r + s)) :
    lie E (r + s) X F = lie E (r + s) (X - toL (skw X)) F + lie E (r + s) (toL (skw X)) F := by
  rw [← LinearMap.add_apply, ← map_add (f := _), sub_add_cancel]

theorem yp_mul {a : ℕ} (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) :
    BlockDerivatives.yp k g * BlockDerivatives.yp k' g' = BlockDerivatives.yp (k * k') (g * g') :=
  InducedTensorMap.cf_mul a k k' g g'

theorem rt_yp_rt {a : ℕ} (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) (φ : Sm E a) :
    rt E a (BlockDerivatives.yp k g) (rt E a (BlockDerivatives.yp k' g') φ) = rt E a (BlockDerivatives.yp (k * k') (g * g')) φ := by
  rw [← yp_mul, map_mul, Module.End.mul_apply]

theorem act_fin_eq {a : ℕ} (h : GL (Fin a) (Af E)) (φ : Sm E a) : act (.fin h) φ = rt E a (BlockDerivatives.yp 1 h) φ := by
  refine Subtype.ext (funext fun x => ?_)
  simp [BlockDerivatives.yp]
  rfl

theorem act_cpt_eq {a : ℕ} (κ : Kinf E a) (φ : Sm E a) : act (.cpt κ) φ = rt E a (BlockDerivatives.yp κ 1) φ := by
  refine Subtype.ext (funext fun x => ?_)
  simp [BlockDerivatives.yp]
  rfl

theorem rt_lie_yp {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (X : Lie E a) :
    ∃ X' : Lie E a, rt E a (BlockDerivatives.yp k g) * lie E a X = lie E a X' * rt E a (BlockDerivatives.yp k g) := by
  refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
  rw [BlockDerivatives.yp, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
  exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwHyp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open scoped Classical

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem mulChi_neg_cancel (w : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E (-w)) (mulChi a (Model.absC E w) ψ) = ψ := by
  have h := ChordArithmetic.mulChi_absC_cancel (E := E) a (-w) ψ
  rwa [neg_neg] at h

theorem isAutSt_tw {V : Submodule ℂ (Sm E a)} (hV : IsAutSt V) (w : ℂ) : IsAutSt (tw V w) := by
  refine ⟨ParabolicProjection.isStable_tw hV.1 w, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h := hV.2 ψ hψ
  let χ := Model.absC E w
  change IsAutForm (mulChi a χ ψ)
  exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring
  }

theorem finGen_tw {V : Submodule ℂ (Sm E a)} (hV : FinGen V) (w : ℂ) : FinGen (tw V w) := by
  obtain ⟨S, hS, hgen⟩ := hV
  refine ⟨S.image (mulChi a (Model.absC E w)), ?_, fun W hW hSW => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS (Finset.mem_coe.2 hy))
  · have hle : V ≤ tw W (-w) := hgen _ (ParabolicProjection.isStable_tw hW (-w)) (fun y hy => by
      have hmem : mulChi a (Model.absC E w) y ∈ W :=
        hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))
      have h : (mulChi a (Model.absC E (-w))).toLinearMap (mulChi a (Model.absC E w) y) ∈ tw W (-w) :=
        Submodule.mem_map_of_mem hmem
      rw [LinearEquiv.coe_coe, mulChi_neg_cancel] at h
      exact h)
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 (hle hψ)
    have e := ChordArithmetic.mulChi_absC_cancel (E := E) a w χ
    simp only [LinearEquiv.coe_coe] at e ⊢
    rw [e]
    exact hχ

theorem infNodup_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (h : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (w : ℂ) :
    ∃ m, HasInfCharGL (tw V w) τ m ∧ m.Nodup := by
  obtain ⟨m, hm, hnd⟩ := h
  exact ⟨m.map (· + w), SpectralAccumulation.Trees.hasInfCharGL_tw hm w, hnd.map (add_left_injective w)⟩

theorem regAll_tw {V : Submodule ℂ (Sm E a)} (hV : RegAll V) (w : ℂ) : RegAll (tw V w) :=
  fun τ => infNodup_tw (hV τ) w

theorem hyp_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (w : ℂ) (hA : IsAutSt V) (hF : FinGen V)
    (hI : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (hR : RegAll V) (hN : SpectralAccumulation.NonPos (tw V w)) (hC : SpectralAccumulation.CentIm (tw V w)) :
    Hyp τ (tw V w) :=
  ⟨isAutSt_tw hA w, finGen_tw hF w, hN, hC, infNodup_tw hI w, regAll_tw hR w⟩

theorem tw_tw_neg (V : Submodule ℂ (Sm E a)) (w : ℂ) : tw (tw V (-w)) w = V := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hχ
    simp only [LinearEquiv.coe_coe]
    rw [ChordArithmetic.mulChi_absC_cancel]
    exact hψ
  · intro hφ
    have h1 : (mulChi a (Model.absC E (-w))).toLinearMap φ ∈ tw V (-w) := Submodule.mem_map_of_mem hφ
    have h2 := Submodule.mem_map_of_mem (f := (mulChi a (Model.absC E w)).toLinearMap) h1
    simp only [LinearEquiv.coe_coe] at h2
    rw [ChordArithmetic.mulChi_absC_cancel] at h2
    exact h2

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

