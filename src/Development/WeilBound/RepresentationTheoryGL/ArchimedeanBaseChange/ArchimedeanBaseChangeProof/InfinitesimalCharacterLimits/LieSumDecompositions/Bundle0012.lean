module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmC
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem inf_piece {a : ℕ} {X : Submodule ℂ (Sm E a)} {σ : (E →+* ℂ) → Multiset ℂ} {sh : ℂ}
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) (hσ : σ ∈ adm mm a)
    (hX : ∀ φ ∈ X, ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ) (τ : E →+* ℂ) :
    HasInfCharGL X τ ((σ τ).map (· + sh)) ∧ ((σ τ).map (· + sh)).Nodup := by
  refine ⟨⟨by rw [Multiset.card_map]; exact (mem_adm.1 hσ τ).2, fun u φ hφ => ?_⟩,
    (Multiset.nodup_of_le (mem_adm.1 hσ τ).1 (hmmN τ)).map (add_left_injective sh)⟩
  rw [hX φ hφ τ u, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun z _ => by simp only [Function.comp_apply]; ring

theorem hyp_left (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) (hpE : pE E (r + s) r c = 0)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) {σ : (E →+* ℂ) → Multiset ℂ} (hσ : σ ∈ adm mm r)
    {z : Module.End ℂ (Sm E r)} (hzc : ∀ o, Commute z (act o))
    (hzE : ∀ φ ∈ LS U T, z φ ∈ Eig (LS U T) σ ((s : ℂ) / 2))
    (hfg : ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → LS U T ≤ W) (τ : E →+* ℂ) :
    Hyp τ (tw ((LS U T).map z) (-(s : ℂ) / 2)) := by
  have hXle : (LS U T).map z ≤ LS U T := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).1
  have hXE : ∀ φ ∈ (LS U T).map z, ∀ τ w, cap τ w φ = ((σ τ).map (fun x => w + (s : ℂ) / 2 + x)).prod • φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).2
  have hinf := inf_piece mm hmmN hσ hXE
  obtain ⟨S₁, hS₁, hgen⟩ := hfg
  have haut : ∀ φ ∈ (LS U T).map z, IsAutForm φ := fun φ hφ => BlockSlices.LS_aut hT φ (hXle hφ)
  refine BlockTwistCharacters.hyp_tw (-(s : ℂ) / 2) ⟨isStable_map (BlockSlices.LS_stable hU hT) hzc, haut⟩ (finGen_map hzc S₁ hS₁ hgen)
    ⟨_, hinf τ⟩ (fun τ' => ⟨_, hinf τ'⟩) ?_ (BlockTwistCharacters.centIm_left _ hpE fun φ hφ => LS_cent hT φ (hXle hφ))
  refine BlockTwistCharacters.nonPos_tw _ _ haut fun φ hφ r' hr' hrr c' hc' => ?_
  have hb := LS_exp hU hNP hT φ (hXle hφ) r' hr' hrr c' hc'
  have hd := d_pos (E := E)
  have h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 := by
    rw [div_le_iff₀ hd]
    linarith
  unfold pE
  have e : (-(s : ℂ) / 2).re = -(s : ℝ) / 2 := by simp
  rw [e]
  push_cast at h2 ⊢
  nlinarith

theorem hyp_right (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) (hpE : pE E (r + s) r c = 0)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) {ρ : (E →+* ℂ) → Multiset ℂ} (hρ : ρ ∈ adm mm s)
    {z : Module.End ℂ (Sm E s)} (hzc : ∀ o, Commute z (act o))
    (hzE : ∀ φ ∈ RS U T, z φ ∈ Eig (RS U T) ρ (-(r : ℂ) / 2))
    (hfg : ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → RS U T ≤ W) (τ : E →+* ℂ) :
    Hyp τ (tw ((RS U T).map z) ((r : ℂ) / 2)) := by
  have hXle : (RS U T).map z ≤ RS U T := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).1
  have hXE : ∀ φ ∈ (RS U T).map z, ∀ τ w, cap τ w φ = ((ρ τ).map (fun x => w + -(r : ℂ) / 2 + x)).prod • φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).2
  have hinf := inf_piece mm hmmN hρ hXE
  obtain ⟨S₁, hS₁, hgen⟩ := hfg
  have haut : ∀ φ ∈ (RS U T).map z, IsAutForm φ := fun φ hφ => BlockSlices.RS_aut hT φ (hXle hφ)
  refine BlockTwistCharacters.hyp_tw ((r : ℂ) / 2) ⟨isStable_map (BlockSlices.RS_stable hU hT) hzc, haut⟩ (finGen_map hzc S₁ hS₁ hgen)
    ⟨_, hinf τ⟩ (fun τ' => ⟨_, hinf τ'⟩) ?_ (BlockTwistCharacters.centIm_right _ hpE fun φ hφ => RS_cent hT φ (hXle hφ))
  refine BlockTwistCharacters.nonPos_tw _ _ haut fun φ hφ r₂ hr₂ hrs c₂ hc₂ => ?_
  have hb := RS_exp hU hNP hT φ (hXle hφ) r₂ hr₂ hrs c₂ hc₂
  have hd := d_pos (E := E)
  have hc := BlockTwistCharacters.re_of_pE (E := E) hpE
  have h2 : c₂.re / (Module.finrank ℚ E : ℝ) ≤
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 - (r : ℝ) * s / 2 := by
    rw [div_le_iff₀ hd]
    have e3 : (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 - (r : ℝ) * s / 2) *
        (Module.finrank ℚ E : ℝ) = (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) *
        (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - (r : ℝ) * s * (Module.finrank ℚ E : ℝ) / 2 := by ring
    rw [e3, ← hc]
    exact hb
  unfold pE
  have e : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
  rw [e]
  push_cast at h2 ⊢
  nlinarith

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFg
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem orbSpan_le {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) {φ : Sm E a} (hφ : φ ∈ V) :
    GlobalTheory.CuspRep.LocEx.orbSpan φ ≤ V :=
  Submodule.span_le.2 (by rintro _ ⟨κ, rfl⟩; exact hV (.cpt κ) φ hφ)

theorem stepA_left (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, hb, -, he⟩ := hx
  have h : ∀ i, ∃ Fi : Finset (Sm E r), (↑Fi : Set (Sm E r)) ⊆ BlockDerivatives.lsF r s (T β) 1 1 ∧
      b i ∈ Submodule.span ℂ (↑Fi : Set (Sm E r)) := fun i => Submodule.mem_span_finite_of_mem_span (hb i)
  choose Fi hFi hbFi using h
  refine ⟨Finset.univ.biUnion Fi, ?_, fun m₂ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.lsF_sub_LS hβ 1 1 (hFi i hi)
  · rw [left_slice_eq_sum (T β) b q he m₂]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.span_mono (fun x hx => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
      (hbFi i)

theorem stepA_right (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, -, hq, he⟩ := hx
  refine ⟨Finset.univ.image q, ?_, fun m₁ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.rsF_sub_RS hβ 1 1 (hq i)
  · rw [right_slice_eq_sum (T β) b q he m₁]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem q (Finset.mem_univ i))))

theorem stepB_left (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₂ : GA E s), sl0 m₂ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) B (BlockDerivatives.LS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun β F F' hFF' h m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₂))
    (fun β hβ => stepA_left hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₂ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E r))).comap (sl0 m₂ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₂
  exact hle hmem

theorem stepB_right (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₁ : GA E r), sl1 m₁ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) B (BlockDerivatives.RS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun β F F' hFF' h m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₁))
    (fun β hβ => stepA_right hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₁ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E s))).comap (sl1 m₁ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₁
  exact hle hmem

theorem right_inv_of_stab (_hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) {ψ₀ : Sm E (r + s)} (hψ₀ : ψ₀ ∈ U)
    {l : GL (Fin (r + s)) (Af E)} (hl : l ∈ JFinTr.stabFin ψ₀) (y : GA E (r + s)) :
    (T ψ₀).1 (y * finGL E (r + s) l) = (T ψ₀).1 y := by
  have h1 : act (.fin l) ψ₀ = ψ₀ := hl
  have h2 := hT.equiv (.fin l) ψ₀ hψ₀
  rw [h1] at h2
  have h3 := congrArg (fun F : Sm E (r + s) => F.1 y) h2
  rw [act_fin_eq, rt_apply, yp_one_fin] at h3
  exact h3.symm

theorem stepC_left (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧ ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E r)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E r) Tf (BlockDerivatives.LS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E r)) => ∀ (κ : Kinf E (r + s)) (m₂ : GA E s),
      sl0 m₂ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun t F F' hFF' h κ m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₂))
    (fun t _ => stepB_left hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₂ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_left (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₂]
  refine hW (.fin a) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem stepC_right (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧ ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E s)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E s) Tf (BlockDerivatives.RS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E s)) => ∀ (κ : Kinf E (r + s)) (m₁ : GA E r),
      sl1 m₁ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun t F F' hFF' h κ m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₁))
    (fun t _ => stepB_right hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₁ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_right (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₁]
  refine hW (.fin b) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem LS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → BlockDerivatives.LS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) S₀ (BlockDerivatives.LS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E r)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_left hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mleft U T W :=
    hS₀ _ (Mleft_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₂, rfl⟩ := lsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₂

theorem RS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → BlockDerivatives.RS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) S₀ (BlockDerivatives.RS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E s)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_right hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mright U T W :=
    hS₀ _ (Mright_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₁, rfl⟩ := rsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₁

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

