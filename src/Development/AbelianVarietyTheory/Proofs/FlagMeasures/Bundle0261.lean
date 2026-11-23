module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHermitianDualQuotientCyclicSplitPlace
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.CyclicQuot

theorem match_of_coprime {A K ι : Type} [CommRing A] [CommRing K] (p : A →+* K) (H : AddSubgroup (ι → A))
    (T k : ℤ) (hc : IsCoprime k T) (y z : ι → A) (hy : T • y ∈ H) (hz : z ∈ H)
    (h : ∀ b, p (z b) = (k : K) * p (y b)) : ∃ z' ∈ H, ∀ b, p (z' b) = p (y b) := by
  obtain ⟨u, w, huw⟩ := hc
  refine ⟨u • z + w • (T • y), H.add_mem (H.zsmul_mem hz u) (H.zsmul_mem hy w), fun b => ?_⟩
  have h' : (u : K) * k + w * T = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huw
  simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_zsmul, h b]
  simp only [zsmul_eq_mul]
  linear_combination (p (y b)) * h'

theorem coprime_sub {T : ℕ} (hT : T.Prime) (i j : Fin T) (hij : i ≠ j) :
    IsCoprime (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) (T : ℤ) := by
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  refine (hp.irreducible.coprime_iff_not_dvd.mpr fun hd => hij ?_).symm
  have hi := i.2
  have hj := j.2
  have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  exact Fin.ext (by omega)

theorem cyclic_of_components {A K ι : Type} [CommRing A] [CommRing K] (sp : A ≃+* K × K) (O : Subring A)
    (e : A) (he : e ∈ O) (hsp : sp e = (1, 0)) (M D : Submodule O (ι → A)) (T : ℕ) (hT : T.Prime)
    (hTD : ∀ y ∈ D, (T : ℤ) • y ∈ M)
    (y₁ : ι → A) (hy₁ : y₁ ∈ D) (h₁ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).1 = (sp (y₁ b)).1)
    (y₂ : ι → A) (hy₂ : y₂ ∈ D) (h₂ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).2 = (sp (y₂ b)).2)
    (hidx : M.toAddSubgroup.relIndex D.toAddSubgroup = T ^ 2) :
    ∃ d ∈ D, ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ M := by
  classical
  let eO : O := ⟨e, he⟩
  let d : ι → A := eO • y₁ + (1 - eO) • y₂
  have hd : d ∈ D := D.add_mem (D.smul_mem _ hy₁) (D.smul_mem _ hy₂)
  have hdb : ∀ b, sp (d b) = ((sp (y₁ b)).1, (sp (y₂ b)).2) := by
    intro b
    have : d b = e * y₁ b + (1 - e) * y₂ b := rfl
    rw [this, map_add (f := _), map_mul, map_mul, map_sub, map_one, hsp]
    ext <;> simp
  let a : Fin T × Fin T → O := fun ij => ((ij.1 : ℕ) : O) * eO + ((ij.2 : ℕ) : O) * (1 - eO)
  have ha : ∀ ij, sp (a ij : A) = (((ij.1 : ℕ) : K), ((ij.2 : ℕ) : K)) := by
    intro ij
    have : (a ij : A) = ((ij.1 : ℕ) : A) * e + ((ij.2 : ℕ) : A) * (1 - e) := by
      simp [a, eO]
    rw [this, map_add (f := _), map_mul, map_mul, map_sub, map_one, hsp, map_natCast, map_natCast]
    ext <;> simp
  let φ : Fin T × Fin T → D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup :=
    fun ij => QuotientAddGroup.mk ⟨a ij • d, D.smul_mem _ hd⟩
  have hcard : Nat.card (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) = T ^ 2 := hidx
  have hfin : Finite (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hT.ne_zero)
  have hinj : Function.Injective φ := by
    intro s t hst
    have hm : -(a s • d) + a t • d ∈ M := QuotientAddGroup.eq.mp hst
    have hc : ∀ b, sp ((-(a s • d) + a t • d) b) =
        ((((t.1 : ℕ) : K) - ((s.1 : ℕ) : K)) * (sp (y₁ b)).1,
          (((t.2 : ℕ) : K) - ((s.2 : ℕ) : K)) * (sp (y₂ b)).2) := by
      intro b
      have : (-(a s • d) + a t • d) b = -((a s : A) * d b) + (a t : A) * d b := rfl
      rw [this, map_add (f := _), map_neg, map_mul, map_mul, ha, ha, hdb]
      ext <;> simp <;> ring
    by_contra hne
    by_cases h1 : t.1 = s.1
    · have h2 : t.2 ≠ s.2 := fun h2 => hne (Prod.ext h1.symm h2.symm)
      refine h₂ (match_of_coprime ((RingHom.snd K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h2) y₂ _ (hTD _ hy₂) hm fun b => ?_)
      have := congrArg Prod.snd (hc b)
      push_cast
      exact this
    · refine h₁ (match_of_coprime ((RingHom.fst K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h1) y₁ _ (hTD _ hy₁) hm fun b => ?_)
      have := congrArg Prod.fst (hc b)
      push_cast
      exact this
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcard]; simp [sq])
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨s, hs⟩ := hbij.2 (QuotientAddGroup.mk ⟨x, hx⟩)
  have hm : -(a s • d) + x ∈ M := QuotientAddGroup.eq.mp hs
  refine ⟨a s, (a s).2, ?_⟩
  rw [sub_eq_neg_add]
  exact hm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem [StarRing E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ e ∈ intV E v, sp e = (1, 0) := by
  have hH : IsHerm (cm.sig : E →+* E) (1 : Matrix (Fin 1) (Fin 1) E) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [cT]
  let L : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hL : ∀ x ∈ L, ∀ b, x b ∈ intOE E := by
    intro x hx b
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨c, by simp [Algebra.smul_def]⟩
  have hloc : ∀ y ∈ loc v L, ∀ b, y b ∈ intV E v := by
    intro y hy b
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact Subring.subset_closure (Or.inl ⟨⟨x b, hL x hx b⟩, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem c.2 hx
  have hone : (fun _ => 1 : Fin 1 → E ⊗[F] v.adicCompletion F) ∈ loc v L :=
    Submodule.subset_span ⟨fun _ => 1, Submodule.subset_span rfl, by funext i; simp⟩
  have hmem := ((GlobalTheory.T.split_place_lattice_components F E cm 1 1 hH (by simp) v sp h1 h2).1 L (fun _ => sp.symm (1, 0))).mpr
    ⟨⟨_, hone, fun b => by simp⟩, ⟨0, zero_mem _, fun b => by simp⟩⟩
  exact ⟨sp.symm (1, 0), hloc _ hmem 0, by simp⟩

theorem smul_mem_loc {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) : ∀ y ∈ loc v (dualL σ J L), (T : ℤ) • y ∈ loc v L := by
  have h0 : ∀ x ∈ dualL σ J L, (T : ℤ) • x ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have := h x hx
      rwa [Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact L.smul_mem c hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h0 x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_zsmul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem local_dual_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 → ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL v hv sp h1 h2 hiff hidx
  obtain ⟨e, he, hsp⟩ := exists_idem cm v sp h1 h2
  obtain ⟨x, hx, hxn⟩ := hL.2.2.2.2 v hv
  have crit := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v sp h1 h2).1 L x
  have n1 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1 :=
    fun h => hxn (crit.mpr ⟨h x hx, hiff.mp h x hx⟩)
  have n2 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2 :=
    fun h => n1 (hiff.mpr h)
  obtain ⟨y₁, hy₁⟩ := not_forall.mp n1
  obtain ⟨y₂, hy₂⟩ := not_forall.mp n2
  obtain ⟨hy₁, h₁⟩ := Classical.not_imp.mp hy₁
  obtain ⟨hy₂, h₂⟩ := Classical.not_imp.mp hy₂
  exact cyclic_of_components sp (intV E v) e he hsp _ _ T hT
    (smul_mem_loc cm.sig J T L hL.2.2.1 v) y₁ hy₁ h₁ y₂ hy₂ h₂ hidx

end GlobalTheory.St.G.CyclicQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth
section
noncomputable section

open MeasureTheory Metric
open scoped Matrix

namespace GlobalTheory.UJGrowth

variable {n : ℕ} {ε : Fin n → Bool}

def ent (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (Formalism.MainNotions.S.uMat g)

theorem ent_closedEmb : Topology.IsClosedEmbedding (ent (ε := ε)) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1

theorem mem_closedBall_iff_entries {x y : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall y R ↔ ∀ i j, ‖x i j - y i j‖ ≤ R := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hR

theorem mem_closedBall_zero_iff_entries {x : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall 0 R ↔ ∀ i j, ‖x i j‖ ≤ R := by
  rw [mem_closedBall_iff_entries hR]
  simp

theorem uMat_inv_mul' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g⁻¹ * g) = Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g from rfl, inv_mul_cancel]
  rfl

theorem uMat_mul_inv' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g * g⁻¹) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

theorem uMat_inv_eq (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.MainNotions.S.uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc Formalism.MainNotions.S.uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g) * Formalism.MainNotions.S.uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv', Matrix.mul_one]

theorem norm_inv_entry (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖Formalism.MainNotions.S.uMat g⁻¹ i j‖ = ‖Formalism.MainNotions.S.uMat g j i‖ := by
  rw [uMat_inv_eq]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem small_ball {S : Subgroup (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (h : (n : ℝ) * (R * (2 * δ)) ≤ 1) (x : Fin n → Fin n → ℂ) :
    μ (ent ⁻¹' (closedBall 0 R ∩ closedBall x δ)) ≤
      μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) := by
  by_cases hex : ∃ s ∈ ent ⁻¹' (closedBall 0 R ∩ closedBall x δ), s ∈ S
  · obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hex
    have hme : MeasurableEmbedding (fun t : Formalism.REAL.UJ ε => s * t) :=
      (Homeomorph.mulLeft s).isClosedEmbedding.measurableEmbedding
    conv_lhs => rw [← hμ.2.2.2 s hs]
    rw [hme.map_apply]
    refine measure_mono fun t ht => ?_
    have ht2 : ent (s * t) ∈ closedBall x δ := ht.2
    have h1 : ent (s * t) ∈ closedBall (ent s) (2 * δ) := by
      have := dist_triangle_right (ent (s * t)) (ent s) x
      rw [mem_closedBall]
      linarith [mem_closedBall.1 ht2, mem_closedBall.1 hs2]
    rw [Set.mem_preimage, mem_closedBall_iff_entries zero_le_one]
    intro i j
    have e : Formalism.MainNotions.S.uMat t = Formalism.MainNotions.S.uMat s⁻¹ * Formalism.MainNotions.S.uMat (s * t) := by
      rw [show Formalism.MainNotions.S.uMat (s * t) = Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat t from rfl, ← Matrix.mul_assoc,
        uMat_inv_mul', Matrix.one_mul]
    have e2 : Formalism.MainNotions.S.uMat t - 1 =
        Formalism.MainNotions.S.uMat s⁻¹ * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) := by
      rw [Matrix.mul_sub, ← e, uMat_inv_mul']
    have e3 : ent t i j - ent (1 : Formalism.REAL.UJ ε) i j = (Formalism.MainNotions.S.uMat t - 1) i j := rfl
    rw [e3, e2, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ l ∈ (Finset.univ : Finset (Fin n)),
        ‖Formalism.MainNotions.S.uMat s⁻¹ i l * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) l j‖ ≤ R * (2 * δ) :=
      fun l _ => by
        rw [norm_mul]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) hR
        · rw [norm_inv_entry]
          exact (mem_closedBall_zero_iff_entries hR).1 hs1 l i
        · exact (mem_closedBall_iff_entries (by linarith)).1 h1 l j
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    simpa using h
  · rw [measure_mono_null (t := (S : Set (Formalism.REAL.UJ ε))ᶜ) (fun s hs hS => hex ⟨s, hs, hS⟩) hμ.2.2.1]
    exact zero_le

end GlobalTheory.UJGrowth

namespace GlobalTheory.UJGrowth

theorem growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε),
    Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ →
    ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R →
      μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  intro n ε S _ μ hμ hfin
  haveI := hμ.1
  have hemb : Topology.IsClosedEmbedding (ent (ε := ε)) := ent_closedEmb
  let ν : Measure (Fin n → Fin n → ℂ) := μ.map ent
  have hνA : ∀ A, MeasurableSet A → ν A = μ (ent ⁻¹' A) := fun A hA =>
    Measure.map_apply hemb.continuous.measurable hA
  have hcpt : ∀ y r, μ (ent ⁻¹' closedBall y r) < ⊤ := fun y r =>
    (hemb.isCompact_preimage (isCompact_closedBall y r)).measure_lt_top
  haveI : SigmaFinite ν := hemb.measurableEmbedding.sigmaFinite_map
  set M := μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) with hM
  have hMf : M ≠ ⊤ := (hcpt _ _).ne
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set d := Module.finrank ℝ (Fin n → Fin n → ℂ)
  let lam : Measure (Fin n → Fin n → ℂ) := Measure.addHaar
  refine ⟨M.toReal * (4 * N) ^ d, 2 * d, fun R hR => ?_⟩
  set δ := (2 * N * R)⁻¹ with hδ
  have hp : 1 ≤ 2 * N * R := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hcond : (n : ℝ) * (R * (2 * δ)) ≤ 1 := by
    have e : (n : ℝ) * (R * (2 * δ)) = n / N := by
      rw [hδ]; field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hsb : ∀ x, ν (closedBall 0 R ∩ closedBall x δ) ≤ M := fun x => by
    rw [hνA _ (measurableSet_closedBall.inter measurableSet_closedBall)]
    exact small_ball hμ (by linarith) hδ0.le hcond x
  have hset : {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} = ent ⁻¹' closedBall 0 R := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff_entries (by linarith)]
    rfl
  rw [hset, ← hνA _ measurableSet_closedBall]
  let W : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) := {p | p.1 ∈ closedBall 0 R ∧ dist p.1 p.2 ≤ δ}
  have hW : MeasurableSet W :=
    ((isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le continuous_dist continuous_const)).measurableSet
  have e1 : (ν.prod lam) W = lam (closedBall 0 δ) * ν (closedBall 0 R) := by
    rw [Measure.prod_apply hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ closedBall (0 : Fin n → Fin n → ℂ) R
    · rw [Set.indicator_of_mem hs, ← Measure.addHaar_closedBall_center lam s]
      congr 1
      ext x
      exact ⟨fun h => mem_closedBall'.2 h.2, fun h => ⟨hs, mem_closedBall'.1 h⟩⟩
    · rw [Set.indicator_of_notMem hs]
      have : Prod.mk s ⁻¹' W = ∅ := by
        ext x
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, hs, false_and, Set.mem_empty_iff_false]
      rw [this, measure_empty]
  have e2 : (ν.prod lam) W ≤ M * lam (closedBall 0 (2 * R)) := by
    rw [Measure.prod_apply_symm hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Fin n → Fin n → ℂ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact hsb x
    · have : (fun s => (s, x)) ⁻¹' W = ∅ := by
        ext s
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, mem_closedBall]
        rintro ⟨h1, h2⟩
        apply hx
        have := dist_triangle_left x 0 s
        rw [mem_closedBall]; linarith
      simp [this]
  rw [e1, Measure.addHaar_closedBall lam _ hδ0.le, Measure.addHaar_closedBall lam _ (by linarith)] at e2
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam _ one_pos).ne' measure_ball_lt_top.ne
  have e3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)) e2
  simp only [ENNReal.toReal_mul] at e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at e3
  have e4 : δ ^ d * (ν (closedBall 0 R)).toReal ≤ M.toReal * (2 * R) ^ d := by
    refine le_of_mul_le_mul_right ?_ hb0
    calc _ = δ ^ d * (lam (ball 0 1)).toReal * (ν (closedBall 0 R)).toReal := by ring
      _ ≤ _ := e3
      _ = _ := by ring
  have e5 : M.toReal * (2 * R) ^ d = δ ^ d * (M.toReal * (4 * N) ^ d * R ^ (2 * d)) := by
    have : 2 * R = δ * (4 * N) * R ^ 2 := by rw [hδ]; field_simp; ring
    rw [this, mul_pow, mul_pow, pow_mul]; ring
  rw [e5] at e4
  have e6 := le_of_mul_le_mul_left e4 (by positivity)
  have hνf : ν (closedBall 0 R) ≠ ⊤ := by
    rw [hνA _ measurableSet_closedBall]; exact (hcpt _ _).ne
  rw [← ENNReal.ofReal_toReal hνf]
  exact ENNReal.ofReal_le_ofReal e6

end GlobalTheory.UJGrowth
end
end

