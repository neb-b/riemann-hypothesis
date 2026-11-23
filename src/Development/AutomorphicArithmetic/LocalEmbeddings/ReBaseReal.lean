module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

section First

open scoped Matrix Classical
open Formalism.BasicNotions.TH
open GlobalTheory.RealLift GlobalTheory.RealLift.LieFirstPf GlobalTheory.RealLift.FirstLine

end First

section Second

open GlobalTheory.RealLift

end Second

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

open GlobalTheory.MajTransport

variable {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d}


open GlobalTheory.RealConjFac in
theorem exists_op {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} (hψ : IsStd ψ)
    (hw : M.IsWeil ψ χX χW om) {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) {h : UA σ W.J} (hh : h ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d), Continuous T ∧
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) ∧
      ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f) := by
  classical
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hψ hw (g, h) hg hh
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hψ hw (g⁻¹, h⁻¹) (inv_mem_UAt hg) (inv_mem_UAt hh)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (T₁ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₁ f) (hT₂ (T₁ f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (T₁ f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, T₁ (T₂ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₂ f) (hT₁ (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₁ (T₂ f)) f).2.2.2.1 _ hc (hid f))
  refine ⟨LinearEquiv.ofLinear T₁ T₂ (LinearMap.ext e12) (LinearMap.ext e21), ?_, fun f => hT₁ f, fun f => hT₂ f⟩
  show Continuous T₁
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  refine GlobalTheory.ArchJointCont.continuous_of_weak T₁ fun T => ?_
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.ArchJointCont.exists_adm F T
  obtain ⟨T', hT'⟩ := hW.adm (g, h) l hl g₀ hg₀
  refine T'.continuous.congr fun f => ?_
  have e1 : om (g, h) (pureA F ⇑f g₀) = pureA F ⇑(T₁ f) g₀ := hT₁ f r₀ (hR₀ f)
  have e2 := hT' f
  rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
  exact e2.symm

end Pair

def reR {a a' : ℕ} (R : RealMaps F a a') (T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a')))
    (T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))) : RealMaps F a a' :=
  ⟨R.Pi, R.p ∘ₗ (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))),
    R.p' ∘ₗ (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))⟩



open GlobalTheory.MajTransport in
theorem polMatch_transport {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {V : Spc F E a} {V' : Spc F E a'} {W : Spc F E (a + a')} (R₂ : RealMaps F a a')
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))}
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    (Rf : FinMaps F a a') {Φ Φ'} (hm : PolMatch B G X (reR R₂ T T') Rf Φ Φ') :
    PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') := by
  have hpol := pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
  have hpol' := pair_pol (Y := V') (Z := W) hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW
  have memT : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ (reG G V V' W).M.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))) hf
    rw [hpol] at this; exact this
  have memT' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ (reG G V V' W).M'.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))) hf
    rw [hpol'] at this; exact this
  obtain ⟨T₀, hT₀, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hsum⟩ := hm
  have hcof : ∀ᶠ v in cofinite, v ∉ T₀ := T₀.finite_toSet.eventually_cofinite_notMem
  refine ⟨T₀, hT₀, m, m', fun i => T (f i), φ, fun j => T' (f' j), φ',
    fun i => ⟨memT _ (hf i).1, (hf i).2.1, (hf i).2.2⟩, fun j => ⟨memT' _ (hf' j).1, (hf' j).2.1, (hf' j).2.2⟩,
    ?_, ?_, hsum⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hΦ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact hT1 (f i) _ (rest_pure (f i) (φ i) (hf i).2.1
        ((hcof.and hT.geo.hM.std).mono fun v hv => ((hf i).2.2 v hv.1).trans hv.2))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hΦ', map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact hT1' (f' j) _ (rest_pure (f' j) (φ' j) (hf' j).2.1
        ((hcof.and hT.geo.hM'.std).mono fun v hv => ((hf' j).2.2 v hv.1).trans hv.2))

end GlobalTheory.ReBase

end
