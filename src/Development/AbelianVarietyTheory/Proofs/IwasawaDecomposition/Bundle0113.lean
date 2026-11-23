module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix Filter

namespace GlobalTheory.CuspRep.LocSph

theorem exists_fixed_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (φ : V) (h0 : φ ≠ 0) (hK : ∀ k ∈ K, ρ k φ = φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add (f := _)] at h5
          have h6 : f i (σ k v - v) = x - ρ k x := by
            rw [map_sub, hf]; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem hx (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem tendsto_sLoc (y : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E)
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : Tendsto (fun v => sLoc E v (y v)) cofinite (𝓝 0) := by
  classical
  have h := (GlobalTheory.Mem.UnrAe.tendsto_finSingle y hy).sub
    (GlobalTheory.Mem.UnrAe.tendsto_finSingle (L := E) (fun _ => 0) fun _ => by simp)
  rw [sub_self] at h
  refine h.congr fun w => ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  change Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w (y w) v -
      Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w 0 v =
      (Pi.single w (y w) : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

theorem tendsto_corner (y : ∀ v : HeightOneSpectrum (𝓞 E), Matrix (Fin a) (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => corner (matN a (sLoc E v)) ((y v).map (v.adicCompletionIntegers E).subtype)) cofinite (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((tendsto_const_nhds (x := (1 : Matrix (Fin a) (Fin a) (Af E)) i j)).sub
    (tendsto_sLoc (E := E) (fun v => (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) fun v => by
      rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _])).add
    (tendsto_sLoc (fun v => (y v i j : v.adicCompletion E)) fun v => (y v i j).2)
  rw [sub_zero, add_zero] at h
  exact h

theorem tendsto_locGL (y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => locGL E a v (GeneralLinearGroup.map (v.adicCompletionIntegers E).subtype (y v))) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (tendsto_corner fun v => (y v).val).prodMk_nhds
    ((MulOpposite.continuous_op.tendsto _).comp (tendsto_corner fun v => ((y v)⁻¹).val))

theorem eventually_mem {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 1) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := by
  have h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype y) ∈ U →
      ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
        locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := fun w => by
    by_contra hc
    push Not at hc
    obtain ⟨-, g, hg⟩ := hc 1
    exact hg (hc g).1
  choose y hy using h
  exact ((tendsto_locGL y).eventually_mem hU).mono fun w hw => hy w hw

variable [_root_.NumberField.IsTotallyComplex E]

def Maps (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ π.V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : π.IsLocComp w σ) : ⨆ f : Maps π w σ, LinearMap.range f.1 = π.V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps π w σ) v, act o (f.1 v) ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => π.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps π w σ) ⟨v, rfl⟩
  refine (π.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps π w σ, LinearMap.range f.1) ≤ (⨆ f : Maps π w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hf⟩ := h
    refine h0 (LinearMap.ext fun v => Subtype.ext ?_)
    have : (f v).1 ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨π.V.subtype ∘ₗ f, fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩ :
        Maps π w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem locComp_spherical : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → ∃ v : σ.V, v ≠ 0 ∧ ∀ g : GL (Fin a) (w.adicCompletionIntegers E), σ.ρ (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) v = v := by
  intro E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨v, h1, h2⟩ := exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
    (fun f : Maps π w σ => f.1) (fun f => f.2.2)
    (Set.range (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype)) φ h0
    (by rintro _ ⟨g, rfl⟩; exact hw g) (by rw [iSup_range_eq π w σ hσ]; exact hφ)
  exact ⟨v, h1, fun g => h2 _ ⟨g, rfl⟩⟩

end GlobalTheory.CuspRep.LocSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulIntegralAtSplitPrime
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory.UnIntApprox

open Filter Topology

theorem exists_near {K : Type} [Field K] [CharZero K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (w : AbsoluteValue K ℝ) {q : K} (hq0 : q ≠ 0) (hq : star q = q⁻¹) (hw : w q < 1)
    (g : Matrix n n K) (hg : IsUnit g.det) :
    ∃ u : Matrix n n K, uᴴ * u = 1 ∧ (∀ i j, w ((g⁻¹ * u - 1) i j) ≤ 1) ∧
      ∀ i j, w ((u⁻¹ * g - 1) i j) ≤ 1 := by
  let ι := Fintype.equivFin n
  obtain ⟨u, hu, hlim⟩ := GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin (Fintype.card n)) _ K))
    conjTranspose_one (by simp) (reindex ι ι g) (fun k => (1 + q ^ k)⁻¹)
  let _ : NormedField K := w.toNormedField
  have hq1 : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw
  have he : Tendsto (fun k : ℕ => (1 + q ^ k)⁻¹) atTop (𝓝 1) := by
    simpa using (hq1.const_add 1).inv₀ (by simp)
  have he' : Tendsto (fun k : ℕ => star (1 + q ^ k)⁻¹) atTop (𝓝 0) := by
    have h := hq1.mul he
    rw [zero_mul] at h
    refine h.congr fun k => ?_
    have hk : q ^ k ≠ 0 := pow_ne_zero _ hq0
    rw [star_inv₀, star_add, star_one, star_pow, hq, inv_pow]
    have : 1 + (q ^ k)⁻¹ = (q ^ k)⁻¹ * (1 + q ^ k) := by field_simp; ring
    rw [this, mul_inv, inv_inv]
  have h1 := hlim w (tendsto_iff_norm_sub_tendsto_zero.1 he) (tendsto_zero_iff_norm_tendsto_zero.1 he')
  let U : ℕ → Matrix n n K := fun k => (u k).submatrix ι ι
  have hU : Tendsto U atTop (𝓝 g) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have h3 := h1 (ι i) (ι j)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] at h3
    exact h3
  have hinv : ContinuousAt Inv.inv g :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg.ne_zero)
  have ha : Tendsto (fun k => g⁻¹ * U k - 1) atTop (𝓝 0) := by
    have := (hU.const_mul g⁻¹).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have hb : Tendsto (fun k => (U k)⁻¹ * g - 1) atTop (𝓝 0) := by
    have := ((hinv.tendsto.comp hU).mul_const g).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have key : ∀ f : ℕ → Matrix n n K, Tendsto f atTop (𝓝 0) → ∀ᶠ k in atTop, ∀ i j, w (f k i j) ≤ 1 := by
    intro f hf
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have := tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hf i) j)
    exact this.eventually_le_const one_pos
  obtain ⟨k, hk1, hk2⟩ := ((key _ ha).and (key _ hb)).exists
  refine ⟨U k, ?_, hk1, hk2⟩
  have h2 : (u k)ᴴ * u k = 1 := by
    have := hu k
    rw [Matrix.mul_one] at this
    exact mul_eq_one_comm.1 this
  show ((u k).submatrix ι ι)ᴴ * (u k).submatrix ι ι = 1
  rw [conjTranspose_submatrix, submatrix_mul_equiv, h2, submatrix_one_equiv]

theorem exists_unitary_mul_integral :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ σ n _ _ 𝔭 α β hσ hα hβ hαβ g hg
  let _ : StarRing K :=
    { star := σ
      star_involutive := hσ
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hβ0 : (β : K) ≠ 0 := by
    intro h
    apply hβ
    have : β = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hα0 : (α : K) ≠ 0 := by
    intro h
    apply hβ0
    rw [hαβ, h, map_zero]
  have hq : star ((α : K) / β) = ((α : K) / β)⁻¹ := by
    show σ _ = _
    rw [map_div₀, ← hαβ, hαβ, hσ, inv_div]
  have hw : NumberField.HeightOneSpectrum.adicAbv K 𝔭 ((α : K) / β) < 1 := by
    rw [map_div₀, ← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding]
    have h1 := (FinitePlace.norm_lt_one_iff_mem K 𝔭 α).2 hα
    have h2 := (FinitePlace.norm_eq_one_iff_notMem K 𝔭 β).2 hβ
    erw [h2]
    rw [div_one]
    exact h1
  obtain ⟨u, hu, h1, h2⟩ := exists_near _ (div_ne_zero hα0 hβ0) hq hw g hg
  obtain ⟨s, hs, hsb⟩ := GlobalTheory.UnApprox.exists_denom (J := (n × n) ⊕ (n × n)) 𝔭.ne_bot
    (Sum.elim (fun p => (g⁻¹ * u - 1) p.1 p.2) (fun p => (u⁻¹ * g - 1) p.1 p.2)) (by
      intro v hv
      have : v = 𝔭 := by
        ext1
        exact (𝔭.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 hv)).symm
      subst this
      rintro (p | p)
      · exact h1 _ _
      · exact h2 _ _)
  have key : ∀ (M : Matrix n n K) (i j : n), (∃ b : 𝓞 K, (s : K) * (M - 1) i j = b) →
      (s : K) * M i j ∈ (algebraMap (𝓞 K) K).range := by
    rintro M i j ⟨b, hb⟩
    refine ⟨b + if i = j then s else 0, ?_⟩
    simp only [Matrix.sub_apply, Matrix.one_apply, mul_sub] at hb
    rw [map_add (f := _)]
    split_ifs at hb ⊢
    · show (b : K) + s = _
      linear_combination -hb
    · rw [map_zero]
      show (b : K) + 0 = _
      linear_combination -hb
  refine ⟨u, hu, s, fun h => 𝔭.isPrime.ne_top ?_, fun i j => key _ _ _ (hsb (Sum.inl (i, j))),
    fun i j => key _ _ _ (hsb (Sum.inr (i, j)))⟩
  have := Ideal.isCoprime_iff_sup_eq.1 hs
  rwa [sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h)] at this

end GlobalTheory.UnIntApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
section
noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

def FinAlg (T : Set ℂ) : Prop :=
  ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧ T ⊆ (Subfield.closure (Z : Set ℂ) : Set ℂ)

theorem FinAlg.mono {T T' : Set ℂ} (h : FinAlg T') (hT : T ⊆ T') : FinAlg T := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, hT.trans hsub⟩

theorem finAlg_of_finite {T : Set ℂ} (h : T.Finite) (ha : ∀ z ∈ T, IsAlgebraic ℚ z) : FinAlg T := by
  refine ⟨h.toFinset, fun z hz => ha z (h.mem_toFinset.mp hz), ?_⟩
  rw [h.coe_toFinset]
  exact Subfield.subset_closure

theorem finAlg_biUnion {κ : Type} {s : Set κ} (hs : s.Finite) {T : κ → Set ℂ} (h : ∀ k ∈ s, FinAlg (T k)) :
    FinAlg (⋃ k ∈ s, T k) := by
  classical
  choose! Z hZ hsub using h
  refine ⟨hs.toFinset.biUnion Z, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact hZ k (hs.mem_toFinset.mp hk) z hzk
  · refine Set.iUnion₂_subset fun k hk => (hsub k hk).trans (Subfield.closure_mono ?_)
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨k, hs.mem_toFinset.mpr hk, hz⟩

theorem FinAlg.union {T T' : Set ℂ} (h : FinAlg T) (h' : FinAlg T') : FinAlg (T ∪ T') := by
  classical
  obtain ⟨Z, hZ, hsub⟩ := h
  obtain ⟨Z', hZ', hsub'⟩ := h'
  refine ⟨Z ∪ Z', fun z hz => ?_, Set.union_subset ?_ ?_⟩
  · rcases Finset.mem_union.mp hz with hz | hz
    · exact hZ z hz
    · exact hZ' z hz
  · exact hsub.trans (Subfield.closure_mono (by simp))
  · exact hsub'.trans (Subfield.closure_mono (by simp))

theorem FinAlg.closure {T : Set ℂ} (h : FinAlg T) : FinAlg (Subfield.closure T : Set ℂ) := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, SetLike.coe_subset_coe.mpr (Subfield.closure_le.mpr hsub)⟩

variable {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ)

def jetSet (n : ℕ) : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b)
    (e : DVar X.Tau a b →₀ ℕ), InRange S M c N N' x ∧ e.degree = n ∧
      z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) e}

def JetAlg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange S M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      IsAlgebraic ℚ ((A.chiF a b N N')⁻¹ * derivAt0 (A.thInd S N N' c x) e)

def VacEq : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

end GlobalTheory.Mem.Col2.JetEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
open Polynomial

namespace GlobalTheory.CuspRep

theorem exists_multiset_qdet {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M)
    (s : ℂ) (φ : M) (f : M →ₗ[ℂ] ℂ) (hf : f φ = 1) :
    ∃ m : Multiset ℂ, Multiset.card m = n ∧ ∀ u, f (Formalism.REAL.qdet F (u + s) φ) = (m.map (u + ·)).prod := by
  classical
  let Q : Finset (Fin n) → ℂ[X] := fun S => ∏ k ∈ Sᶜ, (X - C ((k : ℂ) - s))
  have hQm : ∀ S, (Q S).Monic := fun S => monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hQd : ∀ S, (Q S).natDegree = Sᶜ.card := fun S => by
    simp only [Q]
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  let R : ℂ[X] := ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S
  have h0 : (Q ∅).degree = n := by
    rw [degree_eq_natDegree (hQm _).ne_zero, hQd]; simp
  have hR : R.degree < (Q ∅).degree := by
    rw [h0]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun S hS => ?_)
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S).natDegree < n := by
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [hQd, Finset.card_compl, Fintype.card_fin]
      have h2 := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS))
      have h3 : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    exact_mod_cast h1
  have hm : (Q ∅ + R).Monic := (hQm _).add_of_left hR
  have hd : (Q ∅ + R).natDegree = n := by
    rw [natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hR).trans h0)]
  have hc : Multiset.card (Q ∅ + R).roots = (Q ∅ + R).natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨(Q ∅ + R).roots.map Neg.neg, by rw [Multiset.card_map, hc, hd], fun u => ?_⟩
  have e := congrArg (eval u) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc)
  have e2 : ((Q ∅ + R).roots.map Neg.neg |>.map (u + ·)).prod = eval u (Q ∅ + R) := by
    rw [← e]
    simp [eval_multiset_prod, Multiset.map_map, sub_eq_add_neg]
  have hQe : ∀ S, eval u (Q S) = ∏ k ∈ Sᶜ, (u + s - (k : ℂ)) := fun S => by
    simp only [Q, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [e2, GlobalTheory.CapelliTop.qdet_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))),
    GlobalTheory.CapelliTop.subdet_empty]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [R, eval_add, eval_finsetSum, eval_mul, eval_C, hQe, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_add, map_sum, map_smul, Module.End.one_apply, hf, smul_eq_mul, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun S _ => mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem CuspSub.exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem hasInfChar_infChar_of_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o)) → ∀ (π : CG E a) (τ : E →+* ℂ), π.HasInfChar τ (π.infChar τ) := by
  intro E _ _ _ a hc π τ
  suffices h : ∃ m, π.HasInfChar τ m by
    obtain ⟨m, h⟩ := h
    rwa [h.infChar_eq]
  induction π using Quotient.inductionOn with
  | h π =>
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := a) τ) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (hc τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem isCMFam_host (R : Ranks) (H : Host R) (I : Type) (e : I ≃ R.Psi) :
    IsCMFam (fun i => H.emb (e i).1) := by
  refine ⟨fun i j h => ?_, fun w => ?_⟩
  · rcases NumberField.InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact e.injective (GlobalTheory.CuspAlgComparison.tau_injective H h1)
    · exact absurd h1.symm (GlobalTheory.CuspAlgComparison.tau_ne_conj H (e j) (e i))
  · obtain ⟨τ, h | h⟩ := GlobalTheory.CuspAlgComparison.emb_cases H w.embedding
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      rfl
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      exact (NumberField.InfinitePlace.mk_conjugate_eq _).symm

end GlobalTheory.Mem.Vol
end

