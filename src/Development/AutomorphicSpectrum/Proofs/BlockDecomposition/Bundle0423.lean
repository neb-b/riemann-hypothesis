module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbedding
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

theorem ePG_false_castSucc (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨false, a⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  first
  | (simp [GlobalTheory.BZMir.Leib.ePG, finSumFinEquiv_symm_apply_castSucc]; done)
  | (have h1 : (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1) = Sum.inl a :=
        finSumFinEquiv_symm_apply_castSucc a
     have h2 : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
        finSumFinEquiv (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))
          ((Equiv.sumAssoc (Fin (i + 1)) (Fin (t + 1)) (Fin 1)).symm
            (Sum.map (Equiv.refl (Fin (i + 1))) (Equiv.sumComm (Fin 1) (Fin (t + 1)))
              (Equiv.sumAssoc (Fin (i + 1)) (Fin 1) (Fin (t + 1))
                (Sum.inl (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1)))))) := rfl
     rw [h2, h1]
     simp)

theorem ePG_true_eq (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨true, b⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
  all_goals first | rfl | simp [GlobalTheory.BZMir.Leib.ePG]

section Ent

variable (k : Type) [Field k]

theorem glEmbMat_cc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_lc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_cl (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_ll (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

end Ent

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sEmb_mem_HPG (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) :
    sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∈ HPG k (i + 1) (t + 1) := by
  have hh : ∀ (b : Fin (t + 1)) (a : Fin (i + 1)),
      (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (eGP (i + 1) t ⟨true, b⟩) (eGP (i + 1) t ⟨false, a⟩) = 0 := by
    have hp : ((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) ∈
        parab k (eGP (i + 1) t) := h.2
    rw [mem_parab_iff] at hp
    intro b a
    exact hp true false b a (by decide)
  have hentry : ∀ p q : Fin ((i + 1) + t + 1 + 1),
      (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
          GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 1 + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1 + 1)) (Fin ((i + 1) + t + 1 + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  show ((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
      GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b x y hba
  cases a <;> cases b
  all_goals first | exact absurd hba (by decide) | skip
  refine (hentry _ _).trans ?_
  obtain ⟨c, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (y : Fin (i + 1 + 1))
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    exact hh x c
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]

theorem sEmb_HGP_mem_HPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t), ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧ pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := by
  intro k _ _ _ _ i t h
  let η : GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1) :=
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)),
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_mem_HPG k i t h⟩
  have hη : ∀ p q : Fin ((i + 1) + (t + 1) + 1),
      ((GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η : GL (Fin ((i + 1) + (t + 1) + 1)) k) :
          Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  refine ⟨η, rfl, ?_⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) false p q).trans ?_
    refine (hη _ _).trans ?_
    have hX : ∀ a b : Fin (i + 1),
        (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
            Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b =
          ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
            (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, b⟩) :=
      fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
        (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) false a b
    have hL : ∀ a b : Fin (i + 1 + 1),
        (((GlobalTheory.BZMir.levi k (i + 1) (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 :
            GlobalTheory.BZMir.Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b =
          GlobalTheory.BZMir.glEmbMat k (i + 1)
            (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
              Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := fun _ _ => rfl
    refine Eq.trans ?_ (hL _ _).symm
    obtain ⟨a, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (p : Fin (i + 1 + 1)) <;>
    obtain ⟨b, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (q : Fin (i + 1 + 1))
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
      exact (hX a b).symm
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc]
    · rw [hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll]
  · apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) true p q).trans ?_
    refine (hη _ _).trans ?_
    refine Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) true p q).symm
    rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjUnipotentCharacterCompat
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem gpProj_mirUin_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  intro k _ _ _ _ ψ m j u hh
  obtain ⟨h1, hv⟩ := GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k m (j + 1) ⟨u, hh⟩ u.2
  refine ⟨h1, hv, ?_⟩
  obtain ⟨w', hw'⟩ := id (id hv : (((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) ∈ MirU k (j + 1))
  obtain ⟨w, hw⟩ := (u.2 : ((u : Mir k (m + j + 1)) : GL (Fin (m + j + 1 + 1)) k) ∈ MirU k (m + j + 1))
  rw [mirChar_eq k ψ j ⟨_, hv⟩ w' hw'.symm, mirChar_eq k ψ (m + j) u w hw.symm]
  have hent : ((((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) : Matrix _ _ k)
      (Fin.castSucc (Fin.last j)) (Fin.last (j + 1)) =
      (((u : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k)
        (eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩) (eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩) := by
    show (leviProj k (eGP m (j + 1)) (hgpIncl k m (j + 1) ⟨u, hh⟩) true).val _ _ = _
    rw [leviProj_apply]
    rfl
  have e : eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  rw [blockIndex_true_last, e, ← hw'] at hent
  have a1 := unip_apply_castSucc_last k (j + 1) w' (Fin.last j)
  have a2 := unip_apply_castSucc_last k (m + j + 1) w (Fin.last (m + j))
  have : w'.toAdd (Fin.last j) = w.toAdd (Fin.last (m + j)) := by
    rw [← a1, ← a2]
    refine hent.trans ?_
    exact congrArg (fun g : GL (Fin (m + j + 1 + 1)) k => (g : Matrix (Fin (m + j + 1 + 1)) (Fin (m + j + 1 + 1)) k)
      (Fin.castSucc (Fin.last (m + j))) (Fin.last (m + j + 1))) hw.symm
  rw [this]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwiner
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem cIndSpace_apply_mem_mul {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] {H : Subgroup G}
    {σ : Representation ℂ H W} (f : GlobalTheory.PRep.cIndSpace H σ) (h : G) (hh : h ∈ H)
    (g : G) : f.1.1.1 (h * g) = σ ⟨h, hh⟩ (f.1.1.1 g) := by
  exact f.1.1.2 ⟨h, hh⟩ g

private theorem isHK_empty {G : Type} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H ∅ := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK
  exact ⟨fun _ _ _ => Iff.rfl, ⊤, by simp, fun _ _ _ => Iff.rfl⟩

private theorem isHK_union {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A ∪ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_union, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_union, hA₂ g x hx.1, hB₂ g x hx.2]

private theorem isHK_diff {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A \ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_diff, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_diff, hA₂ g x hx.1, hB₂ g x hx.2]

theorem exists_cInd_restrict_eq {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W') (hι : Continuous ι) (hσ : IsSmooth σ) (hsurj : Function.Surjective q)
    (hH : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (F : cIndSpace H' σ') : ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  classical
  obtain ⟨C, hC, hsupp⟩ : ∃ C : Set G', IsCompact C ∧
      ∀ g, F.1.1.1 g ≠ 0 → ∃ h ∈ H', ∃ c ∈ C, g = h * c := F.2
  have hloc : ∀ c : G', ∃ T : Set G, ∃ U ∈ 𝓝 c, GlobalTheory.CompanionTheory.LeibPhi.IsHK H T ∧
      (∀ y ∈ U, ι y ∈ T) ∧ ∃ e : GlobalTheory.PRep.cIndSpace H σ,
        ∀ x, ι x ∈ T → q (e.1.1.1 (ι x)) = F.1.1.1 x := by
    intro c
    obtain ⟨K', hK'o, hK'⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H' σ' F
    obtain ⟨w, hw⟩ := hsurj (F.1.1.1 c)
    obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_value H σ hσ hbase (ι c) w
    obtain ⟨Ke, hKeo, hKe⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H σ e
    have hS : {y : G' | c⁻¹ * y * c ∈ K' ∧ ι (c⁻¹ * y * c) ∈ Ke} ∈ 𝓝 (1 : G') := by
      have hcont : Continuous (fun y : G' => c⁻¹ * y * c) := by fun_prop
      have hopen : IsOpen {z : G' | z ∈ K' ∧ ι z ∈ Ke} := hK'o.inter (hKeo.preimage hι)
      exact (hopen.preimage hcont).mem_nhds (by simp [one_mem])
    obtain ⟨K, hK, hKemb⟩ := hemb _ hS
    have hconj : (fun μ : G => ι c * μ * (ι c)⁻¹) ⁻¹' K ∈ 𝓝 (1 : G) := by
      have hcont : Continuous (fun μ : G => ι c * μ * (ι c)⁻¹) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    obtain ⟨M, hMo, -, hMsub⟩ := hbase _ hconj
    refine ⟨{g | ∃ a ∈ H, ∃ x ∈ M, g = a * ι c * x}, {y | ι (c⁻¹ * y) ∈ M}, ?_,
      GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H M hMo (ι c), ?_, e, ?_⟩
    · have hcont : Continuous (fun y : G' => ι (c⁻¹ * y)) := hι.comp (continuous_const_mul c⁻¹)
      exact (hMo.preimage hcont).mem_nhds (by simp [one_mem])
    · intro y hy
      exact ⟨1, one_mem _, ι (c⁻¹ * y), hy, by simp⟩
    · rintro x ⟨a, ha, μ, hμ, hx⟩
      have hκ : ι c * μ * (ι c)⁻¹ ∈ K := hMsub hμ
      obtain ⟨h', hh', κ', hκ', hxeq⟩ := hKemb (x * c⁻¹) a ha (ι c * μ * (ι c)⁻¹) hκ
        (by rw [map_mul, hx, map_inv]; group)
      have hx' : x = h' * (c * (c⁻¹ * κ' * c)) := by
        have h0 : x = x * c⁻¹ * c := by group
        rw [h0, hxeq]
        group
      have hι' : ι h' ∈ H := (hH h').1 hh'
      have hFx : F.1.1.1 x = σ' ⟨h', hh'⟩ (q w) := by
        rw [hx', cIndSpace_apply_mem_mul F h' hh', hK' c _ hκ'.1, hw]
      rw [hFx, hx', map_mul, map_mul, cIndSpace_apply_mem_mul e _ hι',
        hKe _ _ hκ'.2, he]
      exact hq ⟨h', hh'⟩ hι' w
  choose T U hU hT hUT e he using hloc
  obtain ⟨t, -, hCt⟩ := hC.elim_nhds_subcover U (fun c _ => hU c)
  have hglue : ∀ s : Finset G', ∃ V : Set G, GlobalTheory.CompanionTheory.LeibPhi.IsHK H V ∧
      (∀ c ∈ s, T c ⊆ V) ∧ ∃ f : GlobalTheory.PRep.cIndSpace H σ,
        (∀ g ∉ V, f.1.1.1 g = 0) ∧ ∀ x, ι x ∈ V → q (f.1.1.1 (ι x)) = F.1.1.1 x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨∅, isHK_empty H, by simp, 0, fun g _ => ?_, fun x hx => ?_⟩
      · rfl
      · simp at hx
    | @insert c s hcs ih =>
      obtain ⟨V, hV, hsV, f, hf0, hf⟩ := ih
      obtain ⟨f', hf'in, hf'out⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H σ
        (isHK_diff (hT c) hV) (e c)
      have hadd : ∀ g, (f + f').1.1.1 g = f.1.1.1 g + f'.1.1.1 g := fun _ => rfl
      refine ⟨V ∪ T c, isHK_union hV (hT c), ?_, f + f', ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Set.subset_union_right
        · exact (hsV d hd).trans Set.subset_union_left
      · intro g hg
        rw [Set.mem_union, not_or] at hg
        rw [hadd, hf0 g hg.1, hf'out g (fun h => hg.2 h.1), add_zero]
      · intro x hx
        by_cases hxV : ι x ∈ V
        · rw [hadd, hf'out _ (fun h => h.2 hxV), add_zero]
          exact hf x hxV
        · rcases hx with hx | hx
          · exact absurd hx hxV
          · rw [hadd, hf0 _ hxV, hf'in _ ⟨hx, hxV⟩, zero_add]
            exact he c x hx
  obtain ⟨V, hV, htV, f, hf0, hf⟩ := hglue t
  refine ⟨f, fun x => ?_⟩
  by_cases hx : ι x ∈ V
  · exact (hf x hx).symm
  · rw [hf0 _ hx, map_zero]
    by_contra hne
    obtain ⟨h', hh', c', hc', rfl⟩ := hsupp x hne
    obtain ⟨d, hd, hc'U⟩ := Set.mem_iUnion₂.1 (hCt hc')
    have hmem : ι c' ∈ V := htV d hd (hUT d c' hc'U)
    unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at hV
    apply hx
    rw [map_mul]
    exact (hV.1 _ ((hH h').1 hh') _).2 hmem

end GlobalTheory.CompanionTheory.LeibPhi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapIntertwinesRestriction
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_cInd_restrict : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  intro G G' W W' _ _ _ _ _ _ _ _ _ _ H H' ι σ σ' q hι hH hq hS hemb hcomp f
  obtain ⟨K', hK'n, hK'c⟩ := hcomp
  obtain ⟨L, hLo, hL⟩ := cInd_right_inv H σ f
  let b : G' → W' := fun x => q (f.1.1.1 (ι x))
  have hind : b ∈ indSpace H' σ' := by
    intro h x
    have hh : ι (h : G') ∈ H := (hH _).1 h.2
    have e : f.1.1.1 (((⟨ι h, hh⟩ : H) : G) * ι x) = σ ⟨ι h, hh⟩ (f.1.1.1 (ι x)) := f.1.1.2 ⟨ι h, hh⟩ (ι x)
    show q (f.1.1.1 (ι ((h : G') * x))) = σ' h (q (f.1.1.1 (ι x)))
    rw [map_mul, ← hq h hh]
    exact congrArg q e
  have hsm : (⟨b, hind⟩ : indSpace H' σ') ∈ smoothPart (ind H' σ') := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H' σ') (L.comap ι)
      (hLo.preimage hι) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show q (f.1.1.1 (ι (g * x))) = q (f.1.1.1 (ι g))
    rw [map_mul, hL (ι g) (ι x) hx]
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H' σ')) ∈ cIndSpace H' σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    have hD : IsCompact (C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}) := hC.inter_right hS
    have key : ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H,
        ∀ n ∈ C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}, ι x = a * n →
        ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c' := by
      refine hD.induction_on
        (p := fun A => ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H, ∀ n ∈ A, ι x = a * n →
          ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c') ?_ ?_ ?_ ?_
      · exact ⟨∅, isCompact_empty, fun _ _ _ n hn => absurd hn (Set.notMem_empty n)⟩
      · rintro A B hAB ⟨C', hC', h⟩
        exact ⟨C', hC', fun x a ha n hn e => h x a ha n (hAB hn) e⟩
      · rintro A B ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
        refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun x a ha n hn e => ?_⟩
        rcases hn with hn | hn
        · obtain ⟨h', hh', c', hc', e'⟩ := h₁ x a ha n hn e
          exact ⟨h', hh', c', Or.inl hc', e'⟩
        · obtain ⟨h', hh', c', hc', e'⟩ := h₂ x a ha n hn e
          exact ⟨h', hh', c', Or.inr hc', e'⟩
      · rintro c ⟨-, h₀, hh₀, s, rfl⟩
        obtain ⟨K, hK, hKe⟩ := hemb K' hK'n
        have hcont : Continuous fun n : G => h₀⁻¹ * n * (ι s)⁻¹ := by fun_prop
        have hN : (fun n : G => h₀⁻¹ * n * (ι s)⁻¹) ⁻¹' K ∈ 𝓝 (h₀ * ι s) := by
          apply hcont.continuousAt.preimage_mem_nhds
          have e : h₀⁻¹ * (h₀ * ι s) * (ι s)⁻¹ = 1 := by group
          rw [e]
          exact hK
        refine ⟨_, mem_nhdsWithin_of_mem_nhds hN, (fun y => y * s) '' K',
          hK'c.image (by fun_prop), fun x a ha n hn e => ?_⟩
        have hn' : h₀⁻¹ * n * (ι s)⁻¹ ∈ K := hn
        have e2 : ι (x * s⁻¹) = (a * h₀) * (h₀⁻¹ * n * (ι s)⁻¹) := by
          rw [map_mul, map_inv, e]
          group
        obtain ⟨h', hh', κ', hκ', e3⟩ := hKe _ _ (mul_mem ha hh₀) _ hn' e2
        refine ⟨h', hh', κ' * s, ⟨κ', hκ', rfl⟩, ?_⟩
        rw [← mul_assoc, ← e3]
        group
    obtain ⟨C', hC', hkey⟩ := key
    refine ⟨C', hC', fun x hx => ?_⟩
    have hne : f.1.1.1 (ι x) ≠ 0 := by
      intro h0
      apply hx
      show q (f.1.1.1 (ι x)) = 0
      rw [h0, map_zero]
    obtain ⟨a, ha, c, hcC, e⟩ := hf (ι x) hne
    refine hkey x a ha c ⟨hcC, a⁻¹, inv_mem ha, x, ?_⟩ e
    rw [e]
    group
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun x => rfl⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsEqEmbedding
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_ratEmb_eq_of_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  intro F E _ _ _ _ _ σ n J g hg
  rw [← range_ratEmb σ J] at hg
  obtain ⟨η, rfl⟩ := hg
  exact ⟨η, rfl⟩

end GlobalTheory.CompanionTheory.CFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVermaStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_vector_mem_low_span_sup_verma : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | exact GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW <;> assumption)
end

