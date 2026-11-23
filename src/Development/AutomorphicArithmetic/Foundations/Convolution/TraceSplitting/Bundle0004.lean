module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

open scoped ComplexConjugate

theorem tyEx_of (hLev : SplitLev) (hSt : SplitStable) (hMa : SplitMatch) (hIn : InertData) (hOff : OffStable)
    (hTyp : TypedEx) (hEig : EigBasic) : TyEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV q w₀ hq S hqS hunr hsph mk
  have h1 : ∀ {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G), IsChr J 1 := fun J =>
    ⟨IsLocallyConstant.const 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm⟩
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  have key : ∀ v : Pl F, ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ)
      (c : ℂ) (f₀ : Gw n v → ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
      (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
      (GM.Split E v → ∀ u, χ u = 1) ∧
      (v ∉ S → v ≠ q → (∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ χ u = 1) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧ UF = GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v = q → (∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        UF = GLnLocal.iwahori (v.adicCompletion F) n) ∧
      (v ∈ S → IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧ IsOpen (UF : Set (Gw n v)) ∧
        UF ≤ GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v ∈ S → ¬ GM.Split E v → (∀ u, RankOne μ V u.1 (J u) (χ u)) ∧
        GM.MatchAt σ v c (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f₀ ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f₀ ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f₀ (y * g) = f₀ g) ∧
      (v ∈ S → GM.Split E v → (∀ g, g ∈ UF ↔ mapGL n (completionMap v (mk v).1) g ∈ J (mk v)) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
        ∀ ψ : Gw n (mk v).1 → ℂ, Test ψ → (∀ u ∈ J (mk v), ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ))
          (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) g) ∧
        ∀ y ∈ UF, ∀ g, ψ (mapGL n (completionMap v (mk v).1) (y * g)) = ψ (mapGL n (completionMap v (mk v).1) g)) := by
    intro v
    obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := hOff F E σ hσ hp n hn v
    by_cases hvS : v ∈ S
    · have hvq : v ≠ q := fun h => hqS (h ▸ hvS)
      by_cases hv : GM.Split E v
      · obtain ⟨U, J, hU, hUle, hJ⟩ := hLev F E σ hσ hp n hn μ V hV v hv
        obtain ⟨s1, s2⟩ := hSt F E σ hσ hp n hn v hv U J fun u => (hJ u).2.1
        obtain ⟨UE, e1, e2, e3⟩ := s2 hU hUle
        obtain ⟨c, hc⟩ := hMa F E σ hσ hp n hn v (mk v) hv U J hU fun u => ⟨(hJ u).1, (hJ u).2.1⟩
        refine ⟨J, fun _ => 1, c, 0, UE, U, fun u => ⟨(hJ u).1, h1 _, ?_⟩, fun x hx => ⟨s1 x hx, rfl⟩, fun _ _ => rfl,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨e2, e3, hU.2, hUle⟩, fun _ h => absurd hv h,
          fun _ _ => ⟨(hJ _).2.1, e1, hc⟩⟩
        rw [(hEig E n μ u.1 _ _ (hJ u).1 (h1 _)).2.1]; exact (hJ u).2.2
      · obtain ⟨J, χ, f, UE, UF, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hIn F E σ hσ hp n hn μ V hV v hv
        exact ⟨J, χ, 1, f, UE, UF, fun u => ⟨(i1 u).1, (i1 u).2.1, (i1 u).2.2.2⟩, i2, fun h => absurd h hv,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨i6, i7, i8, i9⟩,
          fun _ _ => ⟨fun u => (i1 u).2.2.1, i3, i4, i5, i10, i11⟩, fun _ h => absurd h hv⟩
    · have hs : ∀ u : PlacesOver E v, V ⊓ fixL μ u.1 (GLnLocal.integralGL (u.1.adicCompletion E) n) ≠ ⊥ := fun u =>
        hsph u.1 (by rw [show u.1.under (𝓞 F) = v from hu v u]; exact hvS)
      by_cases hvq : v = q
      · refine ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U2, GLnLocal.iwahori (v.adicCompletion F) n,
          fun u => ⟨(o5 u.1).2.1, h1 _, ?_⟩, fun x hx => ⟨o2 x hx, rfl⟩, fun _ _ => rfl, fun _ h => absurd hvq h,
          fun _ => ⟨fun _ => rfl, o4, rfl⟩, fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).2.1 (h1 _)).2.1]
        refine fun h => hs u (eq_bot_iff.2 (h ▸ inf_le_inf_left _ ?_))
        exact biInf_mono fun y hy => Subgroup.map_mono (o5 u.1).2.2 hy
      · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U1,
          GLnLocal.integralGL (v.adicCompletion F) n, fun u => ⟨(o5 u.1).1, h1 _, ?_⟩, fun x hx => ⟨o1 x hx, rfl⟩,
          fun _ _ => rfl, fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, o3, rfl⟩, fun h => absurd h hvq,
          fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).1 (h1 _)).2.1]; exact hs u
  choose J χ c f₀ UE UF k1 k2 k3 k4 k5 k6 k7 k8 using key
  let J' : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  let χ' : ∀ w : Pl E, Gw n w → ℂ := fun w => χ (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), J' u.1 = J v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  have eχ : ∀ v (u : PlacesOver E v), χ' u.1 = χ v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  let T : Ty σ n q w₀ :=
    { S := S, q_not := hqS, J := J', χ := χ', mk' := mk
      co := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).1
      chr := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.1
      off := fun w a b => (k4 _ a b).1 ⟨w, ⟨rfl⟩⟩
      at_q := fun w => (eJ q w).trans ((k5 q rfl).1 w)
      triv := fun v hv w => (eχ v w).trans (k3 v hv w)
      stable := fun v x hx => by simp only [eJ, eχ] at hx ⊢; exact k2 v x hx }
  have hsp : ∀ v, v ∈ T.sp ↔ v ∈ S ∧ GM.Split E v := fun v => Finset.mem_filter
  refine ⟨T, rfl, rfl, hTyp E n μ V hV J' χ' (fun w => ⟨T.co w, T.chr w⟩) ?_ (fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.2),
    fun v hv hn u => ?_, c, f₀, UF, fun v hv g => ?_, fun ψ hψ => ?_⟩
  · have hf : {w : Pl E | w.under (𝓞 F) ∈ insert q S}.Finite := by
      refine ((insert q S).finite_toSet.biUnion fun v _ => Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
      exact Set.mem_biUnion hw ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
    refine Filter.mem_of_superset hf.compl_mem_cofinite fun w hw => ?_
    have hw' : w.under (𝓞 F) ∉ insert q S := hw
    rw [Finset.mem_insert, not_or] at hw'
    exact T.off w hw'.2 hw'.1
  · change RankOne μ V u.1 (J' u.1) (χ' u.1)
    rw [eJ, eχ]; exact (k7 v hv hn).1 u
  · change _ ↔ _ ∈ J' (mk v).1
    rw [eJ]; exact (k8 v ((hsp v).1 hv).1 ((hsp v).1 hv).2).1 g
  · have hψ' : ∀ v ∈ S, GM.Split E v → _ := fun v a b => (k8 v a b).2.2 (ψ v) (hψ v ((hsp v).2 ⟨a, b⟩)).1 (by
      have := (hψ v ((hsp v).2 ⟨a, b⟩)).2
      change ∀ u ∈ J' (mk v).1, _ at this
      rw [eJ] at this; exact this)
    let φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then GM.prodFn (Function.update
          (fun u : PlacesOver E v => ((J v u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) (ψ v))
        else GM.prodFn fun u : PlacesOver E v => (J v u : Set (Gw n u.1)).indicator fun x => conj (χ v u x))
      else if h : v = q then GM.iwFn (h ▸ w₀) 0 else (unitSet E n v).indicator 1
    let f : ∀ v : Pl F, Gw n v → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then fun g => ψ v (mapGL n (completionMap v (mk v).1) g) else f₀ v)
      else if v = q then (GM.iwCoset v 0).indicator 1 else (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1
    let L : GM.Loc σ n q w₀ :=
      { S := S, q_not := hqS, unr := hunr, φ := φ, f := f, c := c, UE := UE, UF := UF
        test := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨(hψ' v hv b).2.1.1, (hψ' v hv b).2.1.2, (hψ' v hv b).2.2.1.1, (hψ' v hv b).2.2.1.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact ⟨(k7 v hv b).2.2.1.1, (k7 v hv b).2.2.1.2, (k7 v hv b).2.2.2.1.1, (k7 v hv b).2.2.2.1.2⟩
        lev := k6
        inv := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨fun y hy => (hψ' v hv b).2.2.2.1 y (((k8 v hv b).2.1 y).1 hy), (hψ' v hv b).2.2.2.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.2.2.2
        mat := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact (hψ' v hv b).1
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.1
        at_q := ⟨by simp only [φ, if_neg hqS, dif_pos], by simp only [f, if_neg hqS, if_pos], (k5 q rfl).2⟩
        off := fun v a b => ⟨by simp only [φ, if_neg a, dif_neg b], by simp only [f, if_neg a, if_neg b], (k4 v a b).2⟩ }
    refine ⟨L, ⟨rfl, hψ, fun v hv => ?_, fun v a b => ?_⟩, fun _ _ => ⟨rfl, rfl⟩, fun v hv => ?_, fun v a b => ?_⟩
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change φ v = GM.prodFn (Function.update (fun u : PlacesOver E v => ((J' u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ))
        (mk v) (ψ v)) ∧ ∀ g, g ∈ UE v ↔ ∀ u, GM.cmp u g ∈ J' u.1
      simp only [eJ, φ, if_pos a, if_pos b, true_and]
      exact (k8 v a b).2.1
    · change φ v = GM.prodFn fun u : PlacesOver E v => (J' u.1 : Set (Gw n u.1)).indicator fun x => conj (χ' u.1 x)
      have a' : v ∈ S := a
      simp only [eJ, eχ, φ, if_pos a', if_neg b]
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change f v = _
      simp only [f, if_pos a, if_pos b]
      rfl
    · change f v = _
      simp only [f, if_pos a, if_neg b]

end UpperTheory.ConvolutionTheory.T
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

section Abs

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

private theorem fixed_of_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (τ : Representation ℂ G X) (hτ : ∀ x, IsOpen {g | τ g x = x})
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (f : X →ₗ[ℂ] H) (hf : ∀ g x, f (τ g x) = π g (f x))
    (v : H) (hv : ∀ u ∈ J, π u v = v) (x : X) (h0 : ⟪v, f x⟫_ℂ ≠ 0) :
    fixedVectors τ J ≠ ⊥ := by
  have hfin : ((fun g => τ g x) '' (J : Set G)).Finite := by
    obtain ⟨t, -, ht⟩ := hJ.elim_nhds_subcover (fun g => {h | τ h x = τ g x}) fun g _ => by
      have h1 : IsOpen ((fun h => g⁻¹ * h) ⁻¹' {g | τ g x = x}) := (hτ x).preimage (by fun_prop)
      refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun h hh => ?_
      have h2 : τ (g⁻¹ * h) x = x := hh
      show τ h x = τ g x
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    refine (t.finite_toSet.image fun g => τ g x).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨i, hi, (h : τ g x = τ i x).symm⟩
  classical
  set S := hfin.toFinset with hS
  have hm : ∀ y, y ∈ S ↔ ∃ g ∈ J, τ g x = y := fun y => by simp [hS]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, (hm x).2 ⟨1, J.one_mem, by simp⟩⟩
  have hc' : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hst : ∀ u ∈ J, ∀ y ∈ S, τ u y ∈ S := fun u hu y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    exact (hm _).2 ⟨u * g, J.mul_mem hu hg, by rw [map_mul]; rfl⟩
  have hy : ∀ y ∈ S, ⟪v, f y⟫_ℂ = ⟪v, f x⟫_ℂ := fun y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    rw [hf]
    have h1 := UnitaryRep.inner_map_map π g v (f x)
    rwa [hv g hg] at h1
  have hmem : (S.card : ℂ)⁻¹ • ∑ y ∈ S, y ∈ fixedVectors τ J := fun u hu => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (τ u) (τ u⁻¹) (hst u hu) (hst _ (J.inv_mem hu)) (fun y _ => ?_) (fun y _ => ?_) fun _ _ => rfl
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  intro hb
  rw [hb, Submodule.mem_bot] at hmem
  have h1 : ⟪v, f ((S.card : ℂ)⁻¹ • ∑ y ∈ S, y)⟫_ℂ = ⟪v, f x⟫_ℂ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, inner_smul_right, map_sum, inner_sum, Finset.sum_congr rfl hy, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [hmem, map_zero, inner_zero_right] at h1
  exact h0 h1.symm

private theorem trace_ne [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsHaarMeasure]
    (τ : Representation ℂ G X) (J : Subgroup G) (hJ : CO J) (hx : fixedVectors τ J ≠ ⊥) {s : ℂ}
    (hs : HasTrace m τ ((J : Set G).indicator 1) s) : s ≠ 0 := by
  obtain ⟨A, hA, hfd, rfl⟩ := hs
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  set c : ℂ := (m.real (J : Set G) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    have h1 : 0 < m (J : Set G) := hJ.2.measure_pos m ⟨1, J.one_mem⟩
    have h2 : m (J : Set G) < ⊤ := hJ.1.measure_lt_top
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h1.ne' h2.ne).ne'
  have hfix : ∀ y ∈ fixedVectors τ J, A y = c • y := fun y hy => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA y l).2, map_smul, smul_eq_mul, sub_eq_zero]
    have e : (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g y)) = (J : Set G).indicator (fun _ => l y) := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, one_mul, hy g hg]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator hmeas, setIntegral_const]
    simp [hcdef]
  have hran : ∀ v, A v ∈ fixedVectors τ J := fun v h hh => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero]
    change (l ∘ₗ τ h) (A v) = _
    rw [(hA v (l ∘ₗ τ h)).2, (hA v l).2]
    refine Eq.trans ?_ (integral_mul_left_eq_self (μ := m) (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g v)) h)
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have hi : (J : Set G).indicator (1 : G → ℂ) (h * g) = (J : Set G).indicator (1 : G → ℂ) g := by
      by_cases hg : g ∈ J
      · rw [Set.indicator_of_mem (show h * g ∈ (J : Set G) from J.mul_mem hh hg),
          Set.indicator_of_mem (show g ∈ (J : Set G) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show h * g ∉ (J : Set G) from fun e => hg ((Subgroup.mul_mem_cancel_left J hh).1 e)),
          Set.indicator_of_notMem (show g ∉ (J : Set G) from hg)]
    show (J : Set G).indicator (1 : G → ℂ) g * l (τ h (τ g v)) = (J : Set G).indicator (1 : G → ℂ) (h * g) * l (τ (h * g) v)
    rw [hi, map_mul, Module.End.mul_apply]
  obtain ⟨x, hxf, hx0⟩ := (Submodule.ne_bot_iff _).1 hx
  have hxr : x ∈ LinearMap.range A :=
    ⟨c⁻¹ • x, by rw [map_smul, hfix x hxf, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have hres : A.restrict (p := LinearMap.range A) (q := LinearMap.range A) (fun v _ => LinearMap.mem_range_self A v) =
      c • LinearMap.id := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    obtain ⟨z, hz⟩ := y.2
    exact hfix y.1 (hz ▸ hran z)
  haveI : FiniteDimensional ℂ (LinearMap.range A) := hfd
  haveI : Nontrivial (LinearMap.range A) :=
    ⟨⟨⟨x, hxr⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]
  exact mul_ne_zero hc (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

end Abs

theorem UpperTheory.ConvolutionTheory.T.unitTrace :
    UpperTheory.ConvolutionTheory.T.UnitTrace := by
  intro K _ _ n μ _ V hV w _ _ m hm τ J hocc hJ hne
  haveI := hm
  have hcl : IsClosed (J : Set (Gw n w)) := J.isClosed_of_isOpen hJ.2
  have hind : ∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
      (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g := by
    intro u hu g
    have h1 : u * g ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_left J hu
    have h2 : g * u ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_right J hu
    by_cases hg : g ∈ J
    · rw [Set.indicator_of_mem (show u * g ∈ (J : Set (Gw n w)) from h1.2 hg),
        Set.indicator_of_mem (show g * u ∈ (J : Set (Gw n w)) from h2.2 hg),
        Set.indicator_of_mem (show g ∈ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
    · rw [Set.indicator_of_notMem (show u * g ∉ (J : Set (Gw n w)) from fun e => hg (h1.1 e)),
        Set.indicator_of_notMem (show g * u ∉ (J : Set (Gw n w)) from fun e => hg (h2.1 e)),
        Set.indicator_of_notMem (show g ∉ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
  have htest : Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ (J : Set (Gw n w))
    · exact ⟨_, hJ.2, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hfix : fixedVectors τ.ρ J ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hvJ : ∀ u ∈ J, locU μ w u v = v := by
      have h1 : v ∈ fixU (locU μ w) J := by
        rw [fixU_locU]
        exact hv.2
      exact h1
    by_contra hbot
    have hle : spanAll τ.ρ (locU μ w) V ≤ (ℂ ∙ v)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, x, rfl⟩
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
      by_contra h
      exact fixed_of_inner (locU μ w) τ.ρ (fun x => τ.smooth x) J hJ.1 f hf.map v hvJ x h hbot
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
      (UpperTheory.summand_le_closure_span_local_type_images K n μ V w τ hV hocc hv.1)
    exact hv0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2))
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w m hV
  obtain ⟨s, hs⟩ := h3 τ hocc _ htest
  exact ⟨hfix, htest, hind, s, trace_ne m τ.ρ J hJ hfix hs, hs⟩
end

