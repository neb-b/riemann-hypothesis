module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreB
section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SatInd
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Tensor

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def evT (ev : ∀ a, X a →ₗ[ℂ] ℂ) : (⨂[ℂ] a, X a) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap ev)

theorem evT_tprod (ev : ∀ a, X a →ₗ[ℂ] ℂ) (x : ∀ a, X a) :
    evT ev (PiTensorProduct.tprod ℂ x) = ∏ a, ev a (x a) := by
  simp [evT]

theorem piTensor_twist (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (χ : ∀ a, Γ a →* ℂˣ) (g : ∀ a, Γ a)
    (y : ⨂[ℂ] a, X a) :
    piTensor (fun a => twist (ρ a) (χ a)) g y = ((∏ a, χ a (g a) : ℂˣ) : ℂ) • piTensor ρ g y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, piTensor_tprod, piTensor_tprod, smul_comm]
    congr 1
    simp only [twist_apply]
    rw [MultilinearMap.map_smul_univ, Units.coe_prod]
    simp only [RingHom.id_apply]
  | add y₁ y₂ h₁ h₂ => rw [map_add (f := _), map_add (f := _), h₁, h₂, smul_add]

end Tensor

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
  {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)}


omit h in
theorem evT_idem (hs : ∀ a, IsSmooth (π a))
    (hC : IsCompact (Subgroup.pi Set.univ (fun a => KO (w.adicCompletion E) (Fin (N a))) :
      Set (∀ a, GL (Fin (N a)) (w.adicCompletion E))))
    (ev : ∀ a, X a →ₗ[ℂ] ℂ) (v : ⨂[ℂ] a, X a)
    (hinv : ∀ (μ κ : ∀ a, GL (Fin (N a)) (w.adicCompletion E)), (∀ a, κ a ∈ KO (w.adicCompletion E) (Fin (N a))) →
      evT ev (piTensor π (μ * κ) v) = evT ev (piTensor π μ v))
    (μ : ∀ a, GL (Fin (N a)) (w.adicCompletion E)) :
    evT ev (piTensor π μ (idem (isSmooth_piTensor hs) hC v)) = evT ev (piTensor π μ v) := by
  let Φ : (⨂[ℂ] a, X a) →ₗ[ℂ] ((∀ a, GL (Fin (N a)) (w.adicCompletion E)) → ℂ) :=
    { toFun := fun y ν => evT ev (piTensor π ν y)
      map_add' := fun y y' => funext fun ν => by simp [map_add (f := _)]
      map_smul' := fun r y => funext fun ν => by simp [map_smul] }
  have hΦs : ∀ y, Φ y ∈ smoothPart (rightReg ℂ (∀ a, GL (Fin (N a)) (w.adicCompletion E)) ℂ) := fun y =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((isSmooth_piTensor hs y).mem_nhds (by simp)) fun g hg =>
      funext fun ν => by
        have hg' : piTensor π g y = y := hg
        show evT ev (piTensor π (ν * g) y) = evT ev (piTensor π ν y)
        rw [map_mul, Module.End.mul_apply, hg'])
  let Φ' : (⨂[ℂ] a, X a) →ₗ[ℂ] smoothPart (rightReg ℂ (∀ a, GL (Fin (N a)) (w.adicCompletion E)) ℂ) :=
    Φ.codRestrict _ hΦs
  have hΦe : ∀ g y, Φ' (piTensor π g y) = smoothRep (rightReg ℂ _ ℂ) g (Φ' y) := fun g y =>
    Subtype.ext (funext fun ν => by
      show evT ev (piTensor π ν (piTensor π g y)) = evT ev (piTensor π (ν * g) y)
      rw [map_mul, Module.End.mul_apply])
  have key := idem_map (isSmooth_piTensor hs) (isSmooth_smoothRep _) hC Φ' hΦe v
  have hfix : Φ' v ∈ fixed (smoothRep (rightReg ℂ (∀ a, GL (Fin (N a)) (w.adicCompletion E)) ℂ))
      (Subgroup.pi Set.univ fun a => KO (w.adicCompletion E) (Fin (N a))) :=
    GlobalTheory.LGrp.mem_fixed.2 fun κ hκ => Subtype.ext (funext fun ν => by
      show evT ev (piTensor π (ν * κ) v) = evT ev (piTensor π ν v)
      exact hinv ν κ fun a => hκ a trivial)
  rw [idem_of_mem _ _ hfix] at key
  exact congrFun (congrArg Subtype.val key) μ

theorem isSatVecGL_of_levi (hs : ∀ a, IsSmooth (π a)) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ a, ∀ x ∈ fixed (π a) (KGL w (n := (N a))), x ≠ 0 → IsSatVecGL w (π a) x (S a))
    (z : Fin c → ℂˣ) (hz : ∀ a, (z a : ℂ) = (qV E w : ℂ) ^ ((modExp (fun a => Fin (N a)) a : ℂ) / 2))
    (ev : ∀ a, X a →ₗ[ℂ] ℂ) (G : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hGK : ∀ g, ∀ k ∈ KGL w (n := n), G (g * k) = G g)
    (hGN : ∀ u ∈ unipRad (w.adicCompletion E) (stdBlocks N h), ∀ g, G (u * g) = G g)
    (v : ⨂[ℂ] a, X a)
    (hGv : ∀ μ : ∀ a, GL (Fin (N a)) (w.adicCompletion E),
      G (leviEmb (w.adicCompletion E) (stdBlocks N h) μ) = evT ev (piTensor π μ v))
    (hG0 : G ≠ 0) :
    IsSatVecGL w (rightReg ℂ _ ℂ) G (∑ a, (S a).map (· * z a)) := by
  classical
  have hKO : ∀ m, KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  let χ : ∀ a, GL (Fin (N a)) (w.adicCompletion E) →* ℂˣ := fun a =>
    detChar (Fin (N a)) (absPow (w.adicCompletion E) (-((modExp (fun a => Fin (N a)) a : ℂ) / 2)))
  let π' : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a) := fun a => twist (π a) (χ a)
  have hs' : ∀ a, IsSmooth (π' a) := fun a =>
    isSmooth_twist (hs a) (isSmoothChar_of_isUnram (isUnram_absPow _ _)).detChar
  have hχK : ∀ a, ∀ g ∈ KO (w.adicCompletion E) (Fin (N a)), χ a g = 1 := fun a g hg =>
    absPow_det_of_mem _ (by rw [hKO]; exact hg)
  have hC : IsCompact (Subgroup.pi Set.univ (fun a => KO (w.adicCompletion E) (Fin (N a))) :
      Set (∀ a, GL (Fin (N a)) (w.adicCompletion E))) := isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  have hsT := isSmooth_piTensor hs
  set P := idem hsT hC with hPdef
  have hPfix : ∀ y, ∀ g : ∀ a, GL (Fin (N a)) (w.adicCompletion E),
      (∀ a, g a ∈ KO (w.adicCompletion E) (Fin (N a))) → piTensor π' g (P y) = P y := fun y g hg => by
    rw [piTensor_twist, Finset.prod_eq_one fun a _ => hχK a _ (hg a), Units.val_one, one_smul]
    exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem hsT hC y) g fun a _ => hg a
  set Bt := ∑ a, (S a).map (· * z a) with hBt
  have hQ : ∀ y, ∀ f : IndSp (stdBlocks N h) (piTensor π'),
      f ∈ fixed (multiProd (stdBlocks N h) π') (KGL w (n := n)) → f.1.1 1 = P y →
      (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (multiProd (stdBlocks N h) π') (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) f =
        satEig (qV E w) n Bt j • f) ∧ (f ≠ 0 → Bt.card = n) := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      intro f hf hf1
      by_cases hf0 : f = 0
      · subst hf0
        refine ⟨fun ϖ hϖ j hj => ?_, fun h0 => absurd rfl h0⟩
        rw [smul_zero]
        exact (SatCompare.heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) _).map_zero
      have hfKO : f ∈ fixed (multiProd (stdBlocks N h) π') (KO (w.adicCompletion E) (Fin n)) := by
        rw [← hKO]; exact hf
      have e1 : f.1.1 1 = r • PiTensorProduct.tprod ℂ fun a => idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a) := by
        rw [hf1, map_smul, hPdef, idem_tprod hs (fun a => GlobalTheory.SplitFlip.isCompact_KO) hC]
      have hx0 : ∀ a, idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a) ≠ 0 := fun a ha => hf0 (by
        refine eq_zero_of_apply_one (stdBlocks N h) hfKO ?_
        rw [e1, MultilinearMap.map_coord_zero _ a ha, smul_zero])
      have hsat : ∀ a, IsSatVecGL w (π' a) (idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a)) ((S a).map (· * z a)) :=
        fun a => isSatVecGL_twist (hS a _ (by rw [hKO]; exact idem_mem _ _ _) (hx0 a)) _ (by rw [hz a, neg_neg])
      have hf' := isSatVecGL_multiProd h hs' hsat hf hf0 e1
      exact ⟨hf'.2.2.2, fun _ => hf'.2.2.1⟩
    | add y₁ y₂ ih₁ ih₂ =>
      intro f hf hf1
      obtain ⟨f₁, hf₁, e₁⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor π') (x := P y₁) (hPfix y₁)
      obtain ⟨f₂, hf₂, e₂⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor π') (x := P y₂) (hPfix y₂)
      have hf₁' : f₁ ∈ fixed (multiProd (stdBlocks N h) π') (KGL w (n := n)) := by rw [hKO]; exact hf₁
      have hf₂' : f₂ ∈ fixed (multiProd (stdBlocks N h) π') (KGL w (n := n)) := by rw [hKO]; exact hf₂
      have hsum : f = f₁ + f₂ := by
        rw [← sub_eq_zero]
        refine eq_zero_of_apply_one (stdBlocks N h) (sub_mem (by rw [← hKO]; exact hf) (add_mem hf₁ hf₂)) ?_
        show f.1.1 1 - (f₁.1.1 1 + f₂.1.1 1) = 0
        rw [hf1, e₁, e₂, map_add (f := _), sub_self]
      obtain ⟨H₁, C₁⟩ := ih₁ f₁ hf₁' e₁
      obtain ⟨H₂, C₂⟩ := ih₂ f₂ hf₂' e₂
      refine ⟨fun ϖ hϖ j hj => ?_, fun h0 => ?_⟩
      · have := (SatCompare.heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j)
          (multiProd (stdBlocks N h) π')).map_add f₁ f₂
        simp only [SatCompare.heckeLin_apply] at this
        rw [hsum, this, H₁ ϖ hϖ j hj, H₂ ϖ hϖ j hj, smul_add]
      · by_cases h1 : f₁ = 0
        · refine C₂ fun h2 => h0 ?_
          rw [hsum, h1, h2, add_zero]
        · exact C₁ h1
  obtain ⟨f, hf, hf1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor π') (x := P v) (hPfix v)
  have hfK : f ∈ fixed (multiProd (stdBlocks N h) π') (KGL w (n := n)) := by rw [hKO]; exact hf
  let Y : IndSp (stdBlocks N h) (piTensor π') →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) :=
    (evT ev).compLeft _ ∘ₗ Submodule.subtype _ ∘ₗ Submodule.subtype _
  have hYe : ∀ g F, Y (multiProd (stdBlocks N h) π' g F) = rightReg ℂ _ ℂ g (Y F) := fun _ _ => rfl
  have hδ : ∀ μ : ∀ a, GL (Fin (N a)) (w.adicCompletion E),
      (deltaHalf (w.adicCompletion E) (fun a => Fin (N a)) μ : ℂ) * ((∏ a, χ a (μ a) : ℂˣ) : ℂ) = 1 := fun μ => by
    rw [← Units.val_mul, deltaHalf_apply, ← Finset.prod_mul_distrib, Finset.prod_eq_one, Units.val_one]
    intro a _
    simp only [χ, detChar_apply, absPow_neg, MonoidHom.inv_apply, mul_inv_cancel]
  have hinv : ∀ (μ κ : ∀ a, GL (Fin (N a)) (w.adicCompletion E)), (∀ a, κ a ∈ KO (w.adicCompletion E) (Fin (N a))) →
      evT ev (piTensor π (μ * κ) v) = evT ev (piTensor π μ v) := fun μ κ hκ => by
    rw [← hGv, ← hGv, map_mul, hGK]
    have := ((LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).1 κ 1 (one_mem _)).2 ⟨hκ, one_mem _⟩
    rw [mul_one] at this
    rw [hKO]; exact this
  have hYG : Y f = G := by
    funext g
    obtain ⟨p, hp, x, hx, rfl⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 g
    rw [hGK _ _ (by rw [hKO]; exact hx)]
    show evT ev (f.1.1 (p * x)) = _
    rw [apply_mul_of_fixed _ hf p hx]
    have hEmb (g : ∀ a, GL (Fin (N a)) (w.adicCompletion E)) :
        leviEmb (w.adicCompletion E) (stdBlocks N h) g ∈ parab (w.adicCompletion E) (stdBlocks N h) :=
      mem_parab_iff.2 fun _ _ i j hab => by
        letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
        simpa [leviEmb, Matrix.reindex_apply] using
          (Matrix.blockDiagonal'_apply_ne
            (fun a => (g a : Matrix (Fin (N a)) (Fin (N a)) (w.adicCompletion E))) i j hab.ne')
    have hdecomp (q : parab (w.adicCompletion E) (stdBlocks N h)) :
        ∃ u ∈ unipRad (w.adicCompletion E) (stdBlocks N h),
          (q : GL (Fin n) (w.adicCompletion E)) =
            leviEmb (w.adicCompletion E) (stdBlocks N h)
              (leviProj (w.adicCompletion E) (stdBlocks N h) q) * u := by
      let L : parab (w.adicCompletion E) (stdBlocks N h) :=
        ⟨leviEmb _ _ (leviProj _ _ q), hEmb _⟩
      refine ⟨((L⁻¹ * q : parab (w.adicCompletion E) (stdBlocks N h)) : GL (Fin n) (w.adicCompletion E)),
        (coe_mem_unipRad _ _).2 ?_, ?_⟩
      · have hL : leviProj (w.adicCompletion E) (stdBlocks N h) L = leviProj (w.adicCompletion E) (stdBlocks N h) q := by
          funext a
          ext i j
          simp [L, leviEmb, Matrix.blockDiagonal'_apply_eq]
        rw [map_mul, map_inv, hL, inv_mul_cancel]
      · rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (mul_inv_cancel_left _ _).symm
    obtain ⟨u, hu, hpu⟩ := hdecomp ⟨p, hp⟩
    have hlaw := parInd_law (stdBlocks N h) (piTensor π') f ⟨p, hp⟩ 1
    rw [mul_one] at hlaw
    generalize leviProj (w.adicCompletion E) (stdBlocks N h) ⟨p, hp⟩ = μ at hpu hlaw
    have hu' : leviEmb (w.adicCompletion E) (stdBlocks N h) μ * u *
        (leviEmb (w.adicCompletion E) (stdBlocks N h) μ)⁻¹ ∈ unipRad (w.adicCompletion E) (stdBlocks N h) := by
      let P : parab (w.adicCompletion E) (stdBlocks N h) := ⟨_, hEmb μ⟩
      let U : parab (w.adicCompletion E) (stdBlocks N h) := ⟨u, unipRad_le_parab _ _ hu⟩
      have hU : leviProj (w.adicCompletion E) (stdBlocks N h) U = 1 := (coe_mem_unipRad _ U).1 hu
      show ((P * U * P⁻¹ : parab (w.adicCompletion E) (stdBlocks N h)) : GL (Fin n) (w.adicCompletion E)) ∈ _
      rw [coe_mem_unipRad, map_mul, map_mul, map_inv, hU, mul_one, mul_inv_cancel]
    have hG1 : G p = G (leviEmb (w.adicCompletion E) (stdBlocks N h) μ) := by
      have e : p = (leviEmb (w.adicCompletion E) (stdBlocks N h) μ * u *
          (leviEmb (w.adicCompletion E) (stdBlocks N h) μ)⁻¹) * leviEmb (w.adicCompletion E) (stdBlocks N h) μ := by
        rw [inv_mul_cancel_right]; exact hpu
      rw [e]
      exact hGN _ hu' _
    rw [hG1, hlaw, hf1, piTensor_twist, smul_smul, map_smul, smul_eq_mul, hδ, one_mul,
      evT_idem hs hC ev v hinv μ, hGv]
  have hfne : f ≠ 0 := fun e => hG0 (by rw [← hYG, e, map_zero])
  obtain ⟨hH, hcard⟩ := hQ v f hfK hf1
  refine ⟨hG0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext fun g => hGK g k hk, hcard hfne, fun ϖ hϖ j hj => ?_⟩
  rw [← hYG, ← map_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) Y hYe f, hH ϖ hϖ j hj, map_smul]

end Completion

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesA
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {R : Type} [CommRing R] {a d₁ d₂ r s : ℕ}

theorem val_stdBlocks_const {d N : ℕ} (h : ∑ _ : Fin d, a = N) (b : Fin d) (i : Fin a) :
    ((stdBlocks (fun _ : Fin d => a) h ⟨b, i⟩ : Fin N) : ℕ) = (b : ℕ) * a + i := by
  rw [stdBlocks_val]
  simp

theorem sum_const_eq {d N : ℕ} (h : ∑ _ : Fin d, a = N) : N = d * a := by
  rw [← h]
  simp

theorem stdBlocks_castAdd (h₁ : ∑ _ : Fin d₁, a = r) (H : ∑ _ : Fin (d₁ + d₂), a = r + s) (b : Fin d₁) (i : Fin a) :
    stdBlocks (fun _ : Fin (d₁ + d₂) => a) H ⟨Fin.castAdd d₂ b, i⟩ = Fin.castAdd s (stdBlocks (fun _ : Fin d₁ => a) h₁ ⟨b, i⟩) := by
  apply Fin.ext
  rw [val_stdBlocks_const, Fin.coe_castAdd, Fin.coe_castAdd, val_stdBlocks_const]

theorem stdBlocks_natAdd (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    (b : Fin d₂) (i : Fin a) :
    stdBlocks (fun _ : Fin (d₁ + d₂) => a) H ⟨Fin.natAdd d₁ b, i⟩ = Fin.natAdd r (stdBlocks (fun _ : Fin d₂ => a) h₂ ⟨b, i⟩) := by
  apply Fin.ext
  simp only [val_stdBlocks_const, Fin.val_natAdd, sum_const_eq h₁]
  ring

theorem lev_cc (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nn (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_cn (m : GL (Fin r) R × GL (Fin s) R) (i : Fin r) (j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.natAdd r j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nc (m : GL (Fin r) R × GL (Fin s) R) (i : Fin s) (j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem unip_col (x : BlockIx (r + s) r → R) (i : Fin (r + s)) (k : Fin r) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) i (Fin.castAdd s k) =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) i (Fin.castAdd s k) := by
  change ((1 : Matrix (Fin (r + s)) (Fin (r + s)) R) + nilM x) i (Fin.castAdd s k) = _
  rw [Matrix.add_apply]
  have h0 : nilM x i (Fin.castAdd s k) = 0 := by
    simp only [nilM, Matrix.of_apply, Fin.coe_castAdd]
    rw [dite_eq_right]
    intro h
    exact absurd h.2 (not_le.2 k.isLt)
  rw [h0, add_zero]

theorem unip_row (x : BlockIx (r + s) r → R) (k : Fin s) (j : Fin (r + s)) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r k) j =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r k) j := by
  change ((1 : Matrix (Fin (r + s)) (Fin (r + s)) R) + nilM x) (Fin.natAdd r k) j = _
  rw [Matrix.add_apply]
  have h0 : nilM x (Fin.natAdd r k) j = 0 := by
    simp only [nilM, Matrix.of_apply, Fin.coe_natAdd]
    rw [dite_eq_right]
    intro h
    omega
  rw [h0, add_zero]

theorem unip_lev_cc (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    ((unip x * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add, unip_col, lev_nc, lev_cc, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, Fin.castAdd_inj, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem unip_lev_nn (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    ((unip x * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp only [Units.val_mul, Matrix.mul_apply, unip_row]
  rw [← Matrix.mul_apply, Matrix.one_mul, lev_nn]

theorem castAdd_or_natAdd (b : Fin (d₁ + d₂)) : (∃ c, b = Fin.castAdd d₂ c) ∨ ∃ c, b = Fin.natAdd d₁ c := by
  rcases lt_or_ge (b : ℕ) d₁ with h | h
  · exact Or.inl ⟨⟨b, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨b - d₁, by omega⟩, Fin.ext ?_⟩
    simp only [Fin.coe_natAdd]
    omega

theorem leviEmb_split (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    (m : ∀ _ : Fin (d₁ + d₂), GL (Fin a) R) :
    leviEmb R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m =
      lev R r s (leviEmb R (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b)),
        leviEmb R (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b))) := by
  have hcn : ∀ (c : Fin d₁) (c' : Fin d₂), Fin.castAdd d₂ c ≠ Fin.natAdd d₁ c' := by
    intro c c' h
    have h1 := congrArg Fin.val h
    have h2 := c.isLt
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  apply Units.ext
  ext p q
  obtain ⟨⟨b, i⟩, rfl⟩ := (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H).surjective p
  obtain ⟨⟨b', j⟩, rfl⟩ := (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H).surjective q
  rcases castAdd_or_natAdd b with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
    rcases castAdd_or_natAdd b' with ⟨c', rfl⟩ | ⟨c', rfl⟩
  · by_cases hc : c = c'
    · subst hc
      rw [leviEmb_apply_same, stdBlocks_castAdd h₁ H, stdBlocks_castAdd h₁ H, lev_cc, leviEmb_apply_same]
    · rw [leviEmb_apply_ne R _ _ (fun h => hc (Fin.castAdd_injective _ _ h)), stdBlocks_castAdd h₁ H,
        stdBlocks_castAdd h₁ H, lev_cc, leviEmb_apply_ne R _ _ hc]
  · rw [leviEmb_apply_ne R _ _ (hcn c c'), stdBlocks_castAdd h₁ H, stdBlocks_natAdd h₁ h₂ H, lev_cn]
  · rw [leviEmb_apply_ne R _ _ (fun h => hcn c' c h.symm), stdBlocks_natAdd h₁ h₂ H,
      stdBlocks_castAdd h₁ H, lev_nc]
  · by_cases hc : c = c'
    · subst hc
      rw [leviEmb_apply_same, stdBlocks_natAdd h₁ h₂ H, stdBlocks_natAdd h₁ h₂ H, lev_nn, leviEmb_apply_same]
    · rw [leviEmb_apply_ne R _ _ (fun h => hc (Fin.natAdd_injective _ _ h)), stdBlocks_natAdd h₁ h₂ H,
        stdBlocks_natAdd h₁ h₂ H, lev_nn, leviEmb_apply_ne R _ _ hc]

theorem unipRad_split (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    {v : GL (Fin (r + s)) R} (hv : v ∈ unipRad R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H)) :
    ∃ (x : BlockIx (r + s) r → R) (v₁ : GL (Fin r) R) (v₂ : GL (Fin s) R),
      v₁ ∈ unipRad R (stdBlocks (fun _ : Fin d₁ => a) h₁) ∧ v₂ ∈ unipRad R (stdBlocks (fun _ : Fin d₂ => a) h₂) ∧
      v = unip x * lev R r s (v₁, v₂) := by
  have low : ∀ g : GL (Fin (r + s)) R, g ∈ parab R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (g : Matrix _ _ R) i j = 0 := by
    intro g hg i j hi hj
    rw [mem_parab_iff] at hg
    have hi' := i.isLt
    obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd r i' :=
      ⟨⟨i - r, by omega⟩, Fin.ext (by simp only [Fin.coe_natAdd]; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = Fin.castAdd s j' := ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨⟨c, i''⟩, rfl⟩ := (stdBlocks (fun _ : Fin d₂ => a) h₂).surjective i'
    obtain ⟨⟨c', j''⟩, rfl⟩ := (stdBlocks (fun _ : Fin d₁ => a) h₁).surjective j'
    rw [← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_castAdd h₁ H]
    apply hg
    have := c'.isLt
    rw [Fin.lt_def]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  obtain ⟨hvP, hvD⟩ := mem_unipRad.1 hv
  have hvP' := mem_parab_iff.1 hvP
  have hinvP : v⁻¹ ∈ parab R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) :=
    (mem_unipRad.1 ((unipRad R _).inv_mem hv)).1
  obtain ⟨x, m, hvm⟩ := GlobalTheory.CompanionTheory.CTFin.IwaFin.exists_unip_mul_lev r s v (low v hvP) (low v⁻¹ hinvP)
  refine ⟨x, m.1, m.2, ?_, ?_, hvm⟩
  · rw [mem_unipRad, mem_parab_iff]
    constructor
    · intro α β i j hβα
      rw [← unip_lev_cc x m, ← hvm, ← stdBlocks_castAdd h₁ H, ← stdBlocks_castAdd h₁ H]
      apply hvP'
      rw [Fin.lt_def] at hβα ⊢
      simpa only [Fin.coe_castAdd] using hβα
    · intro α i j
      rw [← unip_lev_cc x m, ← hvm, ← stdBlocks_castAdd h₁ H, ← stdBlocks_castAdd h₁ H]
      exact hvD _ _ _
  · rw [mem_unipRad, mem_parab_iff]
    constructor
    · intro α β i j hβα
      rw [← unip_lev_nn x m, ← hvm, ← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_natAdd h₁ h₂ H]
      apply hvP'
      rw [Fin.lt_def] at hβα ⊢
      simp only [Fin.coe_natAdd]
      omega
    · intro α i j
      rw [← unip_lev_nn x m, ← hvm, ← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_natAdd h₁ h₂ H]
      exact hvD _ _ _

end PositivityTheory.Rg.Rs.InductionInStages

end
end

