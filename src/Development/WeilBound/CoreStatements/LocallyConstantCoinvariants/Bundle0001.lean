module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
section
noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}


open Classical in
def extZ : SB (RankIn k (Fin n) (Fin d) {n}) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun φ Y := if h : Yᵀ.rank = n then φ.1 ⟨Yᵀ, h⟩ else 0
  map_add' φ ψ := funext fun Y => by by_cases h : Yᵀ.rank = n <;> simp [h, -rank_transpose]
  map_smul' c φ := funext fun Y => by by_cases h : Yᵀ.rank = n <;> simp [h, -rank_transpose]

theorem extZ_pos (φ : SB (RankIn k (Fin n) (Fin d) {n})) {Y : Matrix (Fin n) (Fin d) k} (h : Yᵀ.rank = n) :
    extZ φ Y = φ.1 ⟨Yᵀ, h⟩ := dif_pos h

theorem extZ_neg (φ : SB (RankIn k (Fin n) (Fin d) {n})) {Y : Matrix (Fin n) (Fin d) k} (h : Yᵀ.rank ≠ n) :
    extZ φ Y = 0 := dif_neg h

theorem isOpenEmb : IsOpenEmbedding fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ := by
  have hXo : IsOpen {x : Matrix (Fin d) (Fin n) k | x.rank ∈ ({n} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := Fin n) (b := Fin d) n using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm (Matrix.rank_le_width x) h⟩
  let T : Matrix (Fin d) (Fin n) k ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toFun := transpose, invFun := transpose, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      continuous_toFun := continuous_id.matrix_transpose, continuous_invFun := continuous_id.matrix_transpose }
  exact T.isOpenEmbedding.comp hXo.isOpenEmbedding_subtypeVal

theorem extZ_mem (φ : SB (RankIn k (Fin n) (Fin d) {n})) : extZ φ ∈ SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hi := isOpenEmb (k := k) (n := n) (d := d)
  have hC : IsCompact ((fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1) := φ.2.2.image hi.continuous
  have h0 : ∀ Y ∉ (fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1, extZ φ Y = 0 := fun Y hY => by
    by_cases h : Yᵀ.rank = n
    · rw [extZ_pos φ h]
      exact image_eq_zero_of_notMem_tsupport fun hm => hY ⟨_, hm, rfl⟩
    · exact extZ_neg φ h
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun Y => ?_, HasCompactSupport.intro hC h0⟩
  by_cases h : Yᵀ.rank = n
  · have e := hi.map_nhds_eq ⟨Yᵀ, h⟩
    rw [transpose_transpose] at e
    rw [← e, Filter.eventually_map, extZ_pos φ h]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 ⟨Yᵀ, h⟩] with x hx
    rw [extZ_pos φ (Y := x.1ᵀ) x.2]
    exact hx
  · have hY : Y ∉ (fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1 := by
      rintro ⟨x, -, rfl⟩
      exact h x.2
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hY] with Z hZ
    rw [h0 Z hZ, h0 Y hY]

theorem exists_extZ {Φ : Matrix (Fin n) (Fin d) k → ℂ} (h : Full Φ) : ∃ φ, extZ φ = Φ := by
  refine ⟨⟨_, comp_mem_SB_of_isInducing (isOpenEmb (k := k) (n := n) (d := d)).isInducing ⟨Φ, h.1⟩ isClosed_univ (fun _ => trivial)
    fun Y _ hY => ⟨⟨Yᵀ, (rank_transpose Y).trans (not_not.1 fun e => hY (h.2 Y e))⟩, rfl⟩⟩, funext fun Y => ?_⟩
  by_cases hY : Yᵀ.rank = n
  · exact extZ_pos _ hY
  · rw [extZ_neg _ hY, h.2 Y (by rwa [rank_transpose] at hY)]

theorem extZ_act (μ : kˣ →* ℂˣ) (g : GL (Fin n) k) (h : GL (Fin d) k) (φ : SB (RankIn k (Fin n) (Fin d) {n}))
    (Y : Matrix (Fin n) (Fin d) k) : extZ (omegaOn (Fin n) (Fin d) μ {n} (g, h) φ) Y =
      (omChar (Fin n) (Fin d) μ (g, h) : ℂ) * extZ φ (g.valᵀ * Y * (invT h).val) := by
  have e : (g.valᵀ * Y * (invT h).val)ᵀ = act Yᵀ (g, h) := by
    simp only [act, invT, transpose_mul, MonoidHom.coe_mk, OneHom.coe_mk, transpose_transpose, Matrix.mul_assoc]
  by_cases hY : Yᵀ.rank = n
  · rw [extZ_pos _ hY, extZ_pos φ (by rw [e, rank_act]; exact hY)]
    exact congrArg (fun x => (omChar (Fin n) (Fin d) μ (g, h) : ℂ) * φ.1 x) (Subtype.ext e.symm)
  · rw [extZ_neg _ hY, extZ_neg φ (by rw [e, rank_act]; exact hY), mul_zero]

theorem irr_equiv {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (Γ × G) V} {τ' : Representation ℂ (Γ × G) U} (E : τ.Equiv τ')
    (H : ∀ N : Submodule ℂ U, twRel (τ'.comp (MonoidHom.inl _ _)) 1 ≤ N → (∀ h, ∀ f ∈ N, τ' (1, h) f ∈ N) →
      N = ⊤ ∨ N ≤ twRel (τ'.comp (MonoidHom.inl _ _)) 1)
    (N : Submodule ℂ V) (hR : twRel (τ.comp (MonoidHom.inl _ _)) 1 ≤ N) (hN : ∀ h, ∀ f ∈ N, τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel (τ.comp (MonoidHom.inl _ _)) 1 := by
  have hE : ∀ γ φ, E.toLinearEquiv (τ γ φ) = τ' γ (E.toLinearEquiv φ) := fun γ φ => LinearMap.congr_fun (E.isIntertwining' γ) φ
  have h1 : twRel (τ'.comp (MonoidHom.inl _ _)) 1 ≤ (twRel (τ.comp (MonoidHom.inl _ _)) 1).map E.toLinearEquiv.toLinearMap :=
    Submodule.span_le.2 (by
      rintro _ ⟨g, f, rfl⟩
      obtain ⟨φ, rfl⟩ := E.toLinearEquiv.surjective f
      exact ⟨_, Submodule.subset_span ⟨g, φ, rfl⟩, by rw [map_sub, map_smul]; exact congrArg (· - _) (hE (g, 1) φ)⟩)
  rcases H (N.map E.toLinearEquiv.toLinearMap) (h1.trans (Submodule.map_mono hR)) (by
    rintro h _ ⟨f, hf, rfl⟩
    exact ⟨_, hN h f hf, hE _ f⟩) with h | h
  · exact Or.inl (top_of_map E.toLinearEquiv.toLinearMap (R := ⊥) (fun f hf => E.toLinearEquiv.map_eq_zero_iff.1 hf) bot_le h)
  · refine Or.inr fun f hf => ?_
    obtain ⟨g, hg, e⟩ := h1 (h ⟨f, hf, rfl⟩)
    rwa [← E.toLinearEquiv.injective e]

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
section
noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {om : Rep σ X W} {v : Pl F}
  {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {ν α : (Fv F v)ˣ →* ℂˣ}

theorem augAt_le : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, φ, h, φ₁, h₁, -, rfl⟩
  exact sub_mem h₁ h)

theorem aug_le_map (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) : aug n d ν α ≤ (augAt om v).map ι := Submodule.span_le.2 (by
  rintro _ ⟨g₀, Φ, hΦ, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := hb.2.2 hΦ
  obtain ⟨g, hg, h⟩ := hD.leftOnto g₀
  obtain ⟨φ₁, h₁, ha, e⟩ := h φ hφ
  exact ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, h₁, ha, rfl⟩, by rw [map_sub, e]⟩)

theorem mem_augAt (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (h : ι φ ∈ aug n d ν α) : φ ∈ augAt om v := by
  obtain ⟨ψ, hψ, e⟩ := aug_le_map hb hD h
  rwa [← hb.2.1 (augAt_le hψ) hφ e]

theorem exists_full (hS : SurjSt) (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (h1 : ν ≠ 1) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), Full (ι φ₀) ∧ φ - φ₀ ∈ augAt om v := by
  obtain ⟨Φ₀, h0, h⟩ := hS _ n d ν α hν h1 _ (hb.1 hφ)
  obtain ⟨φ₀, hφ₀, rfl⟩ := hb.2.2 h0.1
  exact ⟨φ₀, hφ₀, h0, mem_augAt hb hD (sub_mem hφ hφ₀) (by rwa [map_sub])⟩

theorem acts_zero (γ : UA σ X.J × UA σ W.J) : Acts (evFin F v) (om γ) (0 : (Fin n × Fin d → Fv F v) → ℂ) 0 := fun r _ => by
  have : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [this, map_zero]

theorem chrW_div_ne {χ χ' : Chr F E} {t : E →ₐ[F] Fv F v} (h : chrW (χ / χ') t ≠ 1) : chrW (χ' / χ) t ≠ 1 := fun e =>
  h (MonoidHom.ext fun x => by
    have := DFunLike.congr_fun e x
    simp only [chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.one_apply] at this ⊢
    rw [map_div, div_eq_one] at this ⊢
    exact this.symm)

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

def GoodSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v)

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfFree
section
noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eq_one_of_smul [IsGalois ℚ E] {v : Pl F} (hv : SplitsFully E v) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (g : Gal(E/ℚ)) (h : g • P = P) : g = 1 := by
  haveI : P.LiesOver (v.asIdeal.under ℤ) := ⟨by rw [P.over_def v.asIdeal, Ideal.under_under]⟩
  have h1 := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (v.asIdeal.under ℤ) P, hv,
    ← IsGalois.card_aut_eq_finrank] at h1
  have h2 := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [h1] at h2
  have h3 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    (mul_left_eq_self₀.1 h2).resolve_right Nat.card_pos.ne'
  exact (Subgroup.mem_bot).1 (Subgroup.card_eq_one.1 h3 ▸ (MulAction.mem_stabilizer_iff.2 h))

def conjQ (h : IsCMExt F E σ) : Gal(E/ℚ) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (σ : E →+* E)
    (Function.Involutive.bijective (f := σ) (cm_conj_conj h))) fun x => by simp

theorem conjQ_apply (h : IsCMExt F E σ) (x : E) : conjQ h x = σ x := rfl

end PositivityTheory.KCo
end
end

