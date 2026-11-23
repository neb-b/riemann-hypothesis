module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0005
public import GroundTheory.PAdicHodge.AInfGalois
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem tensorSp_levi {n : Fin 2 → ℕ} (h : ∑ i, n i = n 0 + n 1) (W₁ : Submodule ℂ (Sm E (n 0)))
    (W₂ : Submodule ℂ (Sm E (n 1))) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) :
    (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp (blkV W₁ W₂) := by
  have := tensorSp_of_tens2 W₁ W₂ hψ
  convert this using 2 with m
  rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]

theorem capR_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₁ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capR (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 0 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
    funext p q
    rw [CapFactor.std_zero, CapFactor.std_zero]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

theorem capS_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₂ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capS (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 1 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
    funext p q
    rw [CapFactor.std_one, CapFactor.std_one]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

theorem casimir_on_parabolic_induction {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M₁ M₂ : Multiset ℂ) (h₁ : HasInfCharGL W₁ τ M₁) (h₂ : HasInfCharGL W₂ τ M₂) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : MemInd2 W₁ W₂ F) :
    cap τ u F = ((M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod) • F := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set c := (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod with hc
  have hlev : ∀ ψ : Sm E (n 0 + n 1), (∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g, ψ.1 (unip x * g) = ψ.1 g) →
      (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ → ∀ p,
      (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) p) = c * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
    intro ψ hψ hT p
    rw [CapFactor.cap_levi E (n 0) (n 1) τ u ψ hψ p]
    have hT' : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := by
      have e : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) =
          (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod • (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) :=
        funext fun p => capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p
      rw [e]
      exact Submodule.smul_mem _ _ hT
    rw [capS_lev W₁ W₂ τ M₂ h₂ _ _ hT' p, capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p, hc]
    ring
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨v, hv, m, k, g, rfl⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h x
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  have hx : leviEmb (Ad E) (stdBlocks n h) m = lev (Ad E) (n 0) (n 1) (m 0, m 1) := by
    rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]
  rw [hx]
  set y := infGL E (n 0 + n 1) (Unitary.toUnits k) * finGL E (n 0 + n 1) g
  have hcomm : Commute (cap τ u) (rt E (n 0 + n 1) y) := by
    rw [map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g)
  set ψ := rt E (n 0 + n 1) y F
  have hψ : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g', ψ.1 (unip x * g') = ψ.1 g' := fun x g' => by
    simp only [ψ, rt_apply, mul_assoc]
    exact hF.1 x _
  have hψT : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := hF.2 k g
  have h3 := hlev ψ hψ hψT (m 0, m 1)
  have h4 : (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1)) =
      (cap τ u F).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1) * y) := by
    rw [← rt_apply, ← Module.End.mul_apply, hcomm.eq]
    rfl
  have hcapInv := (CapStable.capStable E (n 0) (n 1) τ u F).2 hF.1
  rw [mul_assoc, hcapInv, ← h4, h3]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]
  rw [hF.1]

end PositivityTheory.Rg.Rs.PInfInd2A

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.SpehInfChar

namespace PositivityTheory.Rg.Rs

namespace InfinitesimalCharacterAscent

theorem spehExp_rev (d : ℕ) (i : Fin d) : spehExp d i.rev = -spehExp d i := by
  have h := i.2
  simp only [spehExp, Fin.val_rev]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem prod_neg (d : ℕ) (g : ℂ → ℂ) :
    ∏ i : Fin d, g (-(spehExp d i : ℂ)) = ∏ i : Fin d, g (spehExp d i : ℂ) := by
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, spehExp_rev]
  push_cast
  ring_nf

end InfinitesimalCharacterAscent

open InfinitesimalCharacterAscent in
theorem infAsc_holds : InfAsc := by
  intro E _ _ _ N a d V π hV hemb τ m hm
  obtain ⟨hs, ν, hν, f, hfm, hfi, hfe⟩ := hemb
  have hm0 : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    hasInfChar_infChar_of_commute E a (fun τ u o => cap_commute_act τ u o) (CG.mk π) τ
  set m₀ := (CG.mk π).infChar τ with hm₀
  refine ⟨m₀, hm0, GlobalTheory.BcSpehProof.hasInfCharGL_unique hV.ne_bot hm ⟨?_, fun u φ hφ => ?_⟩⟩
  · rw [← hs, Multiset.card_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Multiset.card_map, hm₀, CG.card_infChar]
  have hI : ∀ X, ∀ φ ∈ indForms hs (fun i => π.twist (ν i)), lie E N X φ ∈ indForms hs (fun i => π.twist (ν i)) :=
    fun X φ hφ => lie_mem_indForms _ hs _ X φ hφ
  have hIV : ∀ X, ∀ φ ∈ V, lie E N X φ ∈ V := fun X φ hφ => hV.stable (.lie X) φ hφ
  have hexpo : ∀ i : Fin d, expo (ν i) τ = ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) := fun i =>
    (GlobalTheory.CuspRep.InfType.expo_of_infType E (ν i)).2.1 _ (hν i) τ
  have hmod : ∀ i : Fin d, ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = ((a * spehExp d i : ℝ) : ℂ) := fun i => by
    rw [mul_spehExp]
    push_cast
    rfl
  have hc := cap_indForms (fun _ : Fin d => a) hs (fun i => π.twist (ν i)) τ (fun i => m₀.map (· + expo (ν i) τ))
    (fun i => hm0.twist (ν i)) u (f φ) (hfm φ hφ)
  have e1 : f (cap τ u φ) = cap τ u (f φ) := cap_comm_quot hIV f hfe τ u φ hφ
  set Q := ((∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))).map (u + ·)).prod with hQ
  have hQ' : (∏ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
      u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod) = Q := by
    rw [hQ, prod_map_finset_sum]
    have e : ∀ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
        u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod =
        (m₀.map fun x => u + x + -(spehExp d i : ℂ)).prod := fun i => by
      rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]
      rw [hexpo i, hmod i]
      push_cast
      ring
    rw [Finset.prod_congr rfl fun i _ => e i, prod_neg d (fun t => (m₀.map fun x => u + x + t).prod)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]
    ring
  have hmem : cap τ u φ - Q • φ ∈ V := by
    rw [hm.2 u φ hφ]
    exact V.sub_mem (V.smul_mem _ hφ) (V.smul_mem _ hφ)
  have h0 : f (cap τ u φ - Q • φ) = 0 := by
    rw [map_sub, e1, hc, map_smul, hQ']
    exact sub_self _
  exact sub_eq_zero.1 (hfi _ hmem h0)

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreD
section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem heckeVec_apply {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {F : Sm E N}
    {f : GL (Fin N) (w.adicCompletion E) → ℂ} (hf : f ∈ Hecke ℂ (KGL w (n := N))) (y : GA E N) :
    (heckeVec ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) f F).1 y =
      heckeVec (rightReg ℂ _ ℂ) (KGL w (n := N)) f (fun g => F.1 (y * finGL E N (locGL E N w g))) 1 := by
  have hK := Final.GLintComm E w N
  rw [heckeVec, heckeVec]
  have e1 := ((LinearMap.proj (R := ℂ) (φ := fun _ : GA E N => ℂ) y).comp (Sm E N).subtype).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf ((finRep E N).comp (locGL E N w)) F)
  have e2 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin N) (w.adicCompletion E) => ℂ)
    (1 : GL (Fin N) (w.adicCompletion E))).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf (rightReg ℂ _ ℂ) (fun g => F.1 (y * finGL E N (locGL E N w g))))
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  show f c.out • F.1 (y * finGL E N (locGL E N w c.out)) = f c.out • F.1 (y * finGL E N (locGL E N w (1 * c.out)))
  rw [one_mul]

def evAt {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) : U →ₗ[ℂ] ℂ :=
  LinearMap.proj x ∘ₗ (Sm E m).subtype ∘ₗ U.subtype

theorem exists_tensor {c : ℕ} {n : Fin c → ℕ} (U : ∀ i, Submodule ℂ (Sm E (n i)))
    {Φ : (∀ i, GA E (n i)) → ℂ} (hΦ : Φ ∈ GlobalTheory.BCWords.tensorSp U) :
    ∃ v : ⨂[ℂ] i, U i, ∀ m, Φ m = evT (fun i => evAt (U i) (m i)) v := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨PiTensorProduct.tprod ℂ φ, fun m => by rw [evT_tprod]; rfl⟩
  | zero => exact ⟨0, fun m => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hy
    exact ⟨v + v', fun m => by rw [Pi.add_apply, hv, hv', map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨a • v, fun m => by rw [Pi.smul_apply, hv, map_smul, smul_eq_mul]⟩

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

