module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LevelIndexEq
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0006
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolArith
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar.Cusp.Dict GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem sig_of_sgI {j j' : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin (j + j')) (Fin (j + j')) E)
    (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (h : Aᴴ * (G.map τ)ᵀ * A = sgI j j') :
    ∃ Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
  let Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : Qᴴ * (G.map τ)ᵀ * Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
    have : Qᴴ * (G.map τ)ᵀ * Q = (Aᴴ * (G.map τ)ᵀ * A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      ext a b
      simp [Q, Matrix.mul_apply]
    rw [this, h]
    ext a b
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.diagonal_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    rcases a with a | a <;> rcases b with b | b <;> simp [sgI, sgn, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨Q, fun h0 => ?_, ?_⟩
  · have := congrArg det e
    rw [det_mul, h0, mul_zero, det_diagonal] at this
    refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) this.symm
    simp only [sgn]
    split_ifs <;> simp
  · rw [← diagonal_transpose, ← e]
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul, Matrix.conjTranspose_apply, Complex.star_def]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isotropic_of_sig {r p : ℕ} (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (hs : ∀ τ ∈ Ψ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ))
    (hr : 3 ≤ r) (h0 : 0 < p) (h1 : p < r) : ∃ e : Fin r → E, e ≠ 0 ∧ herm G e e = 0 := by
  classical
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨r - 1, by omega⟩
  let m : Fin r := ⟨1, by omega⟩
  have hm0 : i0 ≠ m := by simp [i0, m, Fin.ext_iff]
  have hm1 : i1 ≠ m := by simp [i1, m, Fin.ext_iff]; omega
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]; omega
  let ε : Fin r → ℤ := fun a => if (a : ℕ) < p then 1 else -1
  have hε : ∀ a, ε a * ε a = 1 := fun a => by simp only [ε]; split_ifs <;> norm_num
  have hεs : ∀ a : Fin r, ((sgn p (a : ℕ) : ℝ) : ℂ) = (ε a : ℂ) := fun a => by
    simp only [ε, sgn]; split_ifs <;> simp
  let π : ℤ := ∏ a ∈ Finset.univ.erase m, ε a
  have hπ : π * π = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun a _ => hε a
  let d : Fin r → E := fun a => if a = m then G.det * π else ε a
  have hdet : (diagonal d).det = G.det := by
    rw [det_diagonal, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Finset.prod_congr rfl
      (g := fun a => (ε a : E)) fun a ha => if_neg (Finset.ne_of_mem_erase ha)]
    simp only [d, if_true]
    rw [← Int.cast_prod, mul_assoc, ← Int.cast_mul, hπ, Int.cast_one, mul_one]
  have hcd : ∀ a, cc (d a) = d a := fun a => by
    have := GlobalTheory.Published.cc_det_of_herm hG
    simp only [d]
    split_ifs
    · simp only [cc, map_mul, map_intCast] at this ⊢; rw [this]
    · simp [cc]
  obtain ⟨P, hP, e⟩ := GlobalTheory.Published.Landherr.of_signature GlobalTheory.QNorm.landherr_and_landherrSt.1 (G' := diagonal d) hG
    (fun a b => by
      by_cases h : a = b
      · subst h; simp [hcd]
      · simp [h, Ne.symm h, cc])
    hd (by rw [hdet]; exact hd) Ψ hΨ
    (fun τ hτ => ⟨p, hs τ hτ, by
      obtain ⟨Q, hQ, e⟩ := hs τ hτ
      have h2 := congrArg det e
      rw [GlobalTheory.Published.gram_eq, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_diagonal,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)] at h2
      simp only [hεs] at h2
      rw [← Int.cast_prod] at h2
      refine ⟨diagonal fun a => if a = m then Q.det else 1, ?_, ?_⟩
      · rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> simp [hQ]
      · rw [GlobalTheory.Published.gram_eq, diagonal_transpose, diagonal_map (map_zero _), diagonal_map (map_zero _),
          diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext a
        rw [hεs]
        by_cases h : a = m
        · subst h
          have hπ' : (π : ℂ) * π = 1 := by exact_mod_cast hπ
          simp only [d, if_true, map_mul, map_intCast]
          linear_combination (π : ℂ) * h2 + (ε m : ℂ) * hπ'
        · simp [d, h]⟩)
    ⟨1, by rw [hdet, div_self hd]; simp [cc]⟩
  refine ⟨P *ᵥ (Pi.single i0 1 + Pi.single i1 1), fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i0
    simp [Pi.single_eq_of_ne h01] at this
  · rw [herm_mulVec', show Pᵀ * G * P.map (ccH E) = diagonal d from e.symm]
    have e0 : d i0 = 1 := by simp [d, hm0, ε, i0, h0]
    have e1 : d i1 = -1 := by
      have : ¬ (r - 1 < p) := by omega
      simp [d, hm1, ε, i1, this]
    simp [herm, cc, diagonal_apply, Pi.single_apply, apply_ite (IsCMField.complexConj E), add_mul, mul_add,
      Finset.sum_add_distrib, h01, h01.symm, e0, e1]

theorem arithIdx : ArithIdx := by
  intro E _ _ _ _ Ψ j j' s G G' L L' ξ 𝔞 hΨ hj hj' hr hG hG' hd hd' hs hs' hL hL' hξ hc hS hS' h𝔞 hN
  have t : ∀ u ∈ Set.range s, ∃ Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram u G Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
    rintro _ ⟨τ, rfl⟩
    exact (hs τ).elim fun A => sig_of_sgI _ _ A
  have t' : ∀ u ∈ Set.range s, ∃ Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram u G' Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
    rintro _ ⟨τ, rfl⟩
    exact (hs' τ).elim fun A => sig_of_sgI _ _ A
  obtain ⟨P, hP, hPG⟩ := (GlobalTheory.selfDual_lattices_one_genus hG hG' hd hd' hL hL' (Or.inr ⟨ξ, hξ, hc, hS, hS'⟩)).2.2
    GlobalTheory.QNorm.landherr_and_landherrSt.1 _root_.GlobalTheory.QNorm.hasseNormSt (Set.range s) hΨ fun u hu => ⟨j, t u hu, t' u hu⟩
  let a : GL (Fin (j + j')) E := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have ha : (a : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * G *
      (a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = G' := hPG.symm
  obtain ⟨aL', haL', hmap, -, t2⟩ := dualTransport E _ G G' a L' ha hL'
  have hg := localToAdelic E _ G L aL' hL haL'
    ((GlobalTheory.selfDual_lattices_one_genus hG hG hd hd haL' hL (Or.inr ⟨ξ, hξ, hc, t2 ξ hS', hS⟩)).2.1 rfl)
  have hI : IsIsotropicHermitianSetting (IsCMField.complexConj E) G := by
    refine ⟨Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one E, ?_, isUnit_iff_ne_zero.2 hd,
      isotropic_of_sig G hG hd _ hΨ t hr hj (by omega)⟩
    ext i k
    exact (hG i k).symm
  have e : conjBy a (levelGrp (ccH E) G' L' 𝔞) = levelGrp (ccH E) G aL' 𝔞 :=
    (levelFacts _ E _ (IsCMField.complexConj E) G' L' 𝔞 hL' (isUnit_iff_ne_zero.2 hd')).2 G a aL' ha hmap
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e]
    exact inf_le_left
  · rw [e]
    exact levelIndexEq _ E _ _ G L aL' 𝔞 hI hL haL' h𝔞 hN hg

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolFam
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sgU_of_iso {j j' N : ℕ} (s : E →+* ℂ) {G G' a : Matrix (Fin N) (Fin N) E} (ha : aᵀ * G * a.map (ccH E) = G')
    {A A' : Matrix (Fin N) (Sg j j') ℂ} {Ai : Matrix (Sg j j') (Fin N) ℂ} (hA : Aᴴ * (G.map s)ᵀ * A = sgI j j')
    (hA' : A'ᴴ * (G'.map s)ᵀ * A' = sgI j j') (hi : A * Ai = 1) : IsSgU (Ai * (a.map s * A')) := by
  have e2 : ((a.map (ccH E)).map s)ᵀ = (a.map s)ᴴ := by
    ext i k
    exact IsCMField.complexEmbedding_complexConj E s _
  have e3 : (a.map s)ᴴ * (G.map s)ᵀ * a.map s = (G'.map s)ᵀ := by
    rw [← ha, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, e2, Matrix.transpose_map, transpose_transpose,
      Matrix.mul_assoc]
  have e4 : A * (Ai * (a.map s * A')) = a.map s * A' := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  unfold IsSgU
  calc _ = (A * (Ai * (a.map s * A')))ᴴ * (G.map s)ᵀ * (A * (Ai * (a.map s * A'))) := by
        rw [← hA, conjTranspose_mul A]
        simp only [Matrix.mul_assoc]
    _ = A'ᴴ * ((a.map s)ᴴ * (G.map s)ᵀ * a.map s) * A' := by
        rw [e4, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e3, hA']

theorem InLevel.form {H : Host E} {l : Level H} {D : Datum H} {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ)
    {form : D.La →ₗ[ℤ] D.La →ₗ[ℤ] ℤ} (hF : form = D.EF ∨ form = -D.EF) (u v : D.La) : form (γ u) (γ v) = form u v := by
  rcases hF with e | e
  · rw [e]
    exact h.1 u v
  · rw [e]
    exact congrArg Neg.neg (h.1 u v)

theorem InLevel.free {H : Host E} {l : Level H} {D : Datum H} {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ) {g : ℕ}
    (R : RiemLat E g D.La) (hF : R.form = D.EF ∨ R.form = -D.EF) (he : R.EqvBy R γ) (v : D.La) : γ v = v := by
  refine rigid_of_congr (reForm R) (reForm_pos _) (fun C => ?_) γ.toLinearMap.toAddMonoidHom
    (reForm_eqv (h.form hF) he) l.M l.three_le h.congr v
  obtain ⟨S, hS₁, hS₂⟩ := short_finite (fun _ : Unit => R) (fun _ => continuous_const) continuous_const () C
  exact hS₁.subset hS₂.self_of_nhds

theorem mfund_of {H : Host E} {l : Level H} {D : Datum H} {Ψ : Type} [Fintype Ψ] {j j' n g N : ℕ}
    {F : UnivFam E Ψ j j' n g D.La} {Γ : Subgroup (D.La ≃ₗ[𝓞 E] D.La)} {FF : Set (Fin n → ℂ)}
    (hF : F.form = D.EF ∨ F.form = -D.EF) (hΓ : ∀ γ, γ ∈ Γ ↔ InLevel l D γ) (hFF : F.IsFundSet Γ FF)
    {e : D.La →ₗ[𝓞 E] (Fin N → E)} (hL : IsLat (LinearMap.range e)) {Γm : Subgroup (GL (Fin N) E)}
    {ρ : GL (Fin N) E → Ψ → Matrix (Sg j j') (Sg j j') ℂ} {Z : (Fin n → ℂ) → Fin n → ℂ}
    (hZ : Set.BijOn Z (ballDom F.q) (ballDom F.q)) (hm : MeasurableSet (Z '' FF))
    (hq : ∀ γ ∈ Γm, ∀ δ : D.La ≃ₗ[𝓞 E] D.La, (∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) →
      ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔ Z t' = moebBall F.q (ρ γ) (Z t)))
    (h1 : ∀ γ ∈ Γm, ∃ δ, InLevel l D δ ∧ ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x)
    (h2 : ∀ δ, InLevel l D δ → ∃ γ ∈ Γm, ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) :
    MFund F.q ρ Γm (Z '' FF) := by
  refine ⟨hm, ?_, fun s hs => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hZ.mapsTo (hFF.2.1 ht)
  · obtain ⟨t, ht, rfl⟩ := hZ.surjOn hs
    obtain ⟨t', ht', δ, hδ, he⟩ := hFF.2.2.1 t ht
    obtain ⟨γ, hγ, hx⟩ := h2 δ ((hΓ δ).1 hδ)
    exact ⟨γ, hγ, t', ht', (hq γ hγ δ hx t ht t' (hFF.2.1 ht')).1 he⟩
  · rintro _ ⟨t, ht, rfl⟩ γ hγ ⟨t', ht', he⟩
    obtain ⟨δ, hδ, hx⟩ := h1 γ hγ
    have h3 := (hq γ hγ δ hx t (hFF.2.1 ht) t' (hFF.2.1 ht')).2 he
    obtain rfl := hFF.2.2.2 t ht t' ht' ⟨δ, (hΓ δ).2 hδ, h3⟩
    have h4 := hδ.free (F.R t) (by rw [F.form_eq]; exact hF) h3
    have h5 : Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E) = LinearMap.id := by
      refine LinearMap.ext_on hL.2 ?_
      rintro _ ⟨x, rfl⟩
      rw [Matrix.toLin'_apply, ← hx, h4]
      rfl
    exact Units.ext (Matrix.toLin'.injective (h5.trans Matrix.toLin'_one.symm))

theorem famVol_of (h1 : MoebVol) (h2 : StdModel) (h3 : ArithIdx) (h4 : LevelDict) : FamVol := by
  intro E _ _ _ H l D D' Ψ _ j j' n g F F' Γ Γ' FF FF' c₀ hj hj' hr hc hσ hrt hF hF' hΓ hΓ' hFF hFF'
  have := H.unram
  have hemb : ∀ (u : 𝓞 E →+* ℂ) (x : 𝓞 E), embOf u (x : E) = u x := fun u x => IsFractionRing.lift_algebraMap _ x
  have hext : ∀ u : E →+* ℂ, embOf (u.comp (algebraMap (𝓞 E) E)) = u := fun u =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hemb _ x)
  have hcov : ∀ u : E →+* ℂ, u ∈ Set.range (fun τ => embOf (F.σ τ)) ∨
      ComplexEmbedding.conjugate u ∈ Set.range (fun τ => embOf (F.σ τ)) := fun u => by
    by_cases h : ∃ τ, F.σ τ = (starRingEnd ℂ).comp (u.comp (algebraMap (𝓞 E) E))
    · obtain ⟨τ, hτ⟩ := h
      exact Or.inr ⟨τ, (congrArg embOf hτ).trans (hext (ComplexEmbedding.conjugate u))⟩
    · obtain ⟨τ, hτ⟩ := (F.cm.2 _).2 h
      exact Or.inl ⟨τ, (congrArg embOf hτ).trans (hext u)⟩
  have hne : Nonempty Ψ := by
    obtain ⟨u⟩ : Nonempty (E →+* ℂ) := inferInstance
    rcases hcov u with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩
  have hξ : ∀ τ, embOf (F.σ τ) (H.rt : E) = Complex.I * (c₀ : ℂ) := fun τ => (hemb _ _).trans (hrt τ)
  obtain ⟨τ₀⟩ := hne
  have : Nonempty Ψ := ⟨τ₀⟩
  have hξ0 : -(H.rt : E) ≠ 0 := neg_ne_zero.2 fun h => by
    have := hξ τ₀
    rw [h, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') this.symm
  have hξc : cc (-(H.rt : E)) = - -(H.rt : E) := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, neg_neg, map_neg, hξ]
    simp)
  obtain ⟨G, e, A, Ai, Z, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h2 E Ψ j j' n g _ H F _ c₀ hc hξ
  obtain ⟨G', e', A', Ai', Z', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2 E Ψ j j' n g _ H F' _ c₀ hc (hσ ▸ hξ)
  rw [hσ] at b6 b9
  obtain ⟨c1, c2, c3⟩ := h4 E H l D _ G e _ _ hF a3 a4 hξ0 a5
  obtain ⟨d1, d2, d3⟩ := h4 E H l D' _ G' e' _ _ hF' b3 b4 hξ0 b5
  have hne : levIdeal l ≠ ⊥ :=
    inf_span_ne_bot l.prod (Nat.cast_ne_zero.2 (by have := l.three_le; omega)) (Nat.cast_ne_zero.2 l.A_pos.ne')
  obtain ⟨a, ha, hle, hidx⟩ := h3 E Ψ j j' _ G G' _ _ _ (levIdeal l) hcov hj hj' hr a1 b1 a2 b2 (fun τ => ⟨_, (a6 τ).1⟩)
    (fun τ => ⟨_, (b6 τ).1⟩) a4 b4 hξ0 hξc c1 d1 hne
    (neat_mono inf_le_left (neat_of_split E H.bar H.bar_eq l.M l.Mb l.three_le l.prod l.coprime))
  obtain ⟨m1, m2⟩ := a8 FF hFF.1 hFF.2.1
  obtain ⟨m3, m4⟩ := b8 FF' hFF'.1 hFF'.2.1
  have f1 := mfund_of (Γm := levelGrp (ccH E) G (LinearMap.range e) (levIdeal l)) hF hΓ hFF a4 a7 m1
    (fun γ hγ => a9 γ (Subgroup.mem_inf.1 hγ).1) c2 c3
  have f2 := mfund_of (Γm := levelGrp (ccH E) G' (LinearMap.range e') (levIdeal l)) hF' hΓ' hFF' b4 b7 m3
    (fun γ hγ => b9 γ (Subgroup.mem_inf.1 hγ).1) d2 d3
  have : Countable (Matrix (Fin (j + j')) (Fin (j + j')) E) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact inferInstanceAs (Countable (Fin (j + j') → Fin (j + j') → E))
  have : Countable (GL (Fin (j + j')) E) :=
    (Units.val_injective.countable : Countable (Matrix (Fin (j + j')) (Fin (j + j')) E)ˣ)
  have canc : ∀ τ (X : Matrix (Fin (j + j')) (Sg j j') ℂ), A τ * (Ai τ * X) = X := fun τ X => by
    rw [← Matrix.mul_assoc, (a6 τ).2.2, Matrix.one_mul]
  have canc' : ∀ τ (X : Matrix (Fin (j + j')) (Sg j j') ℂ), A' τ * (Ai' τ * X) = X := fun τ X => by
    rw [← Matrix.mul_assoc, (b6 τ).2.2, Matrix.one_mul]
  rw [← m2, ← m4]
  refine h1 Ψ j j' n F.q F'.q _ (rho (fun τ => embOf (F.σ τ)) A Ai) (rho (fun τ => embOf (F.σ τ)) A' Ai')
    (fun τ => Ai τ * ((a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) * A' τ)) (uGrp (ccH E) G)
    (levelGrp (ccH E) G (LinearMap.range e) (levIdeal l)) (levelGrp (ccH E) G' (LinearMap.range e') (levIdeal l)) a _ _
    (fun τ => ?_) (fun x y τ => ?_) (fun γ hγ τ => sgU_of_iso _ hγ (a6 τ).1 (a6 τ).1 (a6 τ).2.2)
    (fun γ hγ τ => sgU_of_iso _ (Subgroup.mem_inf.1 hγ).1 (b6 τ).1 (b6 τ).1 (b6 τ).2.2) (fun τ => sgU_of_iso _ ha (a6 τ).1 (b6 τ).1 (a6 τ).2.2)
    (fun γ τ => ?_) inf_le_left hle hidx f1 f2
  · rw [rho, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, (a6 τ).2.1]
  · simp only [rho, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, canc]
  · have : ((a⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) *
        ((a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) * A' τ) = A' τ := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    simp only [rho, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, canc, canc', this]

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolLevel
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol
open scoped nonZeroDivisors

section

variable {E : Type} [Field E] [NumberField E] {N : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {e : Λ →ₗ[𝓞 E] (Fin N → E)}

theorem lat_multiple (hL : IsLat (LinearMap.range e)) (v : Fin N → E) : ∃ (s : (𝓞 E)⁰) (x : Λ), s • v = e x := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E
    (LinearMap.range e : Set (Fin N → E)) v (hL.2 ▸ Submodule.mem_top)
  rw [Submodule.span_eq] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨s, x, hx.symm⟩

theorem lat_extend (hi : Function.Injective e) (hL : IsLat (LinearMap.range e)) (f : Λ →ₗ[𝓞 E] (Fin N → E)) :
    ∃ g : (Fin N → E) →ₗ[E] (Fin N → E), ∀ x, g (e x) = f x := by
  have hu : ∀ s : (𝓞 E)⁰, IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) (Fin N → E)) s) := by
    have := isLocalizedModule_id (𝓞 E)⁰ (Fin N → E) E
    exact IsLocalizedModule.map_units (LinearMap.id : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))
  have : IsLocalizedModule (𝓞 E)⁰ e :=
    { map_units := hu
      surj := fun v => by
        obtain ⟨s, x, h⟩ := lat_multiple hL v
        exact ⟨(x, s), h⟩
      exists_of_eq := fun h => ⟨1, by rw [hi h]⟩ }
  exact ⟨(IsLocalizedModule.lift (𝓞 E)⁰ e f hu).extendScalarsOfIsLocalization (𝓞 E)⁰ E,
    fun x => IsLocalizedModule.lift_apply (𝓞 E)⁰ e f hu x⟩

theorem lat_matrix (hi : Function.Injective e) (hL : IsLat (LinearMap.range e)) (δ : Λ ≃ₗ[𝓞 E] Λ) :
    ∃ γ : GL (Fin N) E, ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x := by
  obtain ⟨g, hg⟩ := lat_extend hi hL (e ∘ₗ δ.toLinearMap)
  obtain ⟨g', hg'⟩ := lat_extend hi hL (e ∘ₗ δ.symm.toLinearMap)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hg hg'
  have h1 : g ∘ₗ g' = LinearMap.id := LinearMap.ext_on hL.2 (by
    rintro _ ⟨x, rfl⟩
    simp [hg, hg'])
  have h2 : g' ∘ₗ g = LinearMap.id := LinearMap.ext_on hL.2 (by
    rintro _ ⟨x, rfl⟩
    simp [hg, hg'])
  refine ⟨⟨LinearMap.toMatrix' g, LinearMap.toMatrix' g', ?_, ?_⟩, fun x => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id]
  · show _ = LinearMap.toMatrix' g *ᵥ e x
    rw [LinearMap.toMatrix'_mulVec, hg]

omit [NumberField E] in
theorem mem_smul_range (hi : Function.Injective e) (I : Ideal (𝓞 E)) (x : Λ) :
    e x ∈ I • LinearMap.range e ↔ x ∈ I • (⊤ : Submodule (𝓞 E) Λ) := by
  rw [← Submodule.map_top, ← Submodule.map_smul'']
  exact ⟨fun ⟨y, hy, h⟩ => hi h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in
theorem congr_iff (hi : Function.Injective e) {δ : Λ ≃ₗ[𝓞 E] Λ} {γ : Matrix (Fin N) (Fin N) E}
    (h : ∀ x, e (δ x) = γ *ᵥ e x) (M : ℕ) (x : Λ) :
    (∃ y ∈ LinearMap.range e, γ *ᵥ e x = e x + M • y) ↔ ∃ y, δ x = x + M • y := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, hy⟩
    exact ⟨y, hi (by rw [h, hy, map_add (f := _), map_nsmul])⟩
  · rintro ⟨y, hy⟩
    exact ⟨e y, ⟨y, rfl⟩, by rw [← h, hy, map_add (f := _), map_nsmul]⟩

variable [IsCMField E]

theorem herm_smul_smul (G : Matrix (Fin N) (Fin N) E) (a b : E) (x y : Fin N → E) :
    herm G (a • x) (b • y) = a * cc b * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem eq_of_herm_lat (hL : IsLat (LinearMap.range e)) {G G' : Matrix (Fin N) (Fin N) E}
    (h : ∀ x y, herm G (e x) (e y) = herm G' (e x) (e y)) : G = G' := by
  have h1 : ∀ u v, herm G u v = herm G' u v := fun u v => by
    obtain ⟨s, x, hx⟩ := lat_multiple hL u
    obtain ⟨t, y, hy⟩ := lat_multiple hL v
    have hs : ((s : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    have ht : ((t : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero t
    have ht' : cc ((t : 𝓞 E) : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 ht
    have e1 : e x = ((s : 𝓞 E) : E) • u := hx.symm
    have e2 : e y = ((t : 𝓞 E) : E) • v := hy.symm
    have := h x y
    rw [e1, e2, herm_smul_smul, herm_smul_smul] at this
    exact mul_left_cancel₀ (mul_ne_zero hs ht') this
  ext c d
  have e0 : ∀ G : Matrix (Fin N) (Fin N) E, herm G (Pi.single c 1) (Pi.single d 1) = G c d := fun G => by
    simp [herm, cc, Pi.single_apply, apply_ite (IsCMField.complexConj E)]
  rw [← e0 G, ← e0 G', h1]

theorem herm_eq_of_trace {ξ : E} (hξ : ξ ≠ 0) {G G' : Matrix (Fin N) (Fin N) E}
    (h : ∀ x y, EFf ξ G (e x) (e y) = EFf ξ G' (e x) (e y)) (x y : Λ) : herm G (e x) (e y) = herm G' (e x) (e y) := by
  have h0 : -ξ * (herm G (e x) (e y) - herm G' (e x) (e y)) = 0 := by
    refine GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.trace_zero_of_int _ fun a => ?_
    have h1 := h (a • x) y
    have e1 : e (a • x) = (a : E) • e x := by rw [map_smul]; rfl
    have e2 : ∀ G : Matrix (Fin N) (Fin N) E, herm G ((a : E) • e x) (e y) = a * herm G (e x) (e y) := fun G => by
      have := herm_smul_smul G (a : E) 1 (e x) (e y)
      rwa [one_smul, cc, map_one, mul_one] at this
    rw [EFf, EFf, e1, e2, e2, ← sub_eq_zero, ← map_sub] at h1
    rw [← h1]
    congr 1
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left (neg_ne_zero.2 hξ))

end

theorem levelDict : LevelDict := by
  intro E _ _ _ H l D N G e ξ form hF hi hL hξ hf
  have hbij : Function.Bijective form := by
    rcases hF with rfl | rfl
    · exact D.unimod
    · exact neg_involutive.bijective.comp D.unimod
  have hpres : ∀ δ : D.La ≃ₗ[𝓞 E] D.La,
      (∀ a b, D.EF (δ a) (δ b) = D.EF a b) ↔ ∀ a b, form (δ a) (δ b) = form a b := fun δ => by
    rcases hF with rfl | rfl
    · rfl
    · simp
  have hM : 0 < l.M := by have := l.three_le; omega
  have hcong : ∀ (δ : D.La ≃ₗ[𝓞 E] D.La) (γ : Matrix (Fin N) (Fin N) E), (∀ x, e (δ x) = γ *ᵥ e x) →
      (((∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ y, δ a = a + l.M • y) ∧
        ∀ a, ∃ y, δ a = a + l.A • y) ↔
        ∀ x ∈ LinearMap.range e, γ *ᵥ x - x ∈ levIdeal l • LinearMap.range e) := fun δ γ h => by
    refine Iff.trans ?_ (levelIdeal E N (LinearMap.range e) _ l.Mb l.M l.A γ hL hM l.prod (by
      rintro _ ⟨x, rfl⟩
      exact ⟨δ x, h x⟩))
    refine and_congr ⟨fun h1 x hx => ?_, fun h1 a ha => ?_⟩ ⟨?_, fun h1 a => ?_⟩
    · obtain ⟨a, rfl⟩ := Submodule.smul_le_right hx
      exact (congr_iff hi h _ _).2 (h1 a ((mem_smul_range hi _ _).1 hx))
    · exact (congr_iff hi h _ _).1 (h1 _ ((mem_smul_range hi _ _).2 ha))
    · rintro h1 _ ⟨a, rfl⟩
      exact (congr_iff hi h _ _).2 (h1 a)
    · exact (congr_iff hi h _ _).1 (h1 _ ⟨a, rfl⟩)
  refine ⟨⟨?_, fun φ => ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨form x y, (hf x y).symm⟩
  · obtain ⟨x, hx⟩ := hbij.2 (φ.comp e.rangeRestrict.toAddMonoidHom).toIntLinearMap
    refine ⟨e x, ⟨x, rfl⟩, ?_⟩
    rintro ⟨_, y, rfl⟩
    rw [← hf, hx]
    rfl
  · rintro γ ⟨hu, hs, hc⟩
    let φ := LinearEquiv.ofInjective e hi
    let γ₀ : (Fin N → E) ≃ₗ[𝓞 E] (Fin N → E) :=
      (Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv.restrictScalars (𝓞 E)
    have hγ₀ : ∀ v, γ₀ v = (γ : Matrix (Fin N) (Fin N) E) *ᵥ v := fun _ => rfl
    have hm : (LinearMap.range e).map γ₀.toLinearMap = LinearMap.range e := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hs u).1 hu
      · intro hv
        refine ⟨γ₀.symm v, (hs _).2 ?_, γ₀.apply_symm_apply v⟩
        rw [← hγ₀, γ₀.apply_symm_apply]
        exact hv
    let δ : D.La ≃ₗ[𝓞 E] D.La := φ.trans ((γ₀.ofSubmodules _ _ hm).trans φ.symm)
    have hδ : ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x := fun x =>
      congrArg Subtype.val (φ.apply_symm_apply ((γ₀.ofSubmodules _ _ hm) (φ x)))
    refine ⟨δ, ⟨(hpres δ).2 fun a b => ?_, (hcong δ _ hδ).2 hc⟩, hδ⟩
    have : ((form (δ a) (δ b) : ℤ) : ℚ) = form a b := by
      rw [hf, hf, hδ, hδ, EFf, EFf, herm_mulVec', show _ * G * _ = G from hu]
    exact_mod_cast this
  · rintro δ ⟨h1, h2⟩
    obtain ⟨γ, hγ⟩ := lat_matrix hi hL δ
    refine ⟨γ, ⟨?_, fun v => ⟨?_, fun hv => ?_⟩, (hcong δ _ hγ).1 h2⟩, hγ⟩
    · refine eq_of_herm_lat hL (herm_eq_of_trace hξ fun x y => ?_)
      rw [EFf, ← herm_mulVec', ← hγ, ← hγ, ← EFf, ← hf, ← hf, (hpres δ).1 h1]
    · rintro ⟨x, rfl⟩
      exact ⟨δ x, hγ x⟩
    · obtain ⟨y, hy⟩ := hv
      refine ⟨δ.symm y, ?_⟩
      have h3 := hγ (δ.symm y)
      rw [δ.apply_symm_apply, hy] at h3
      have h4 := congrArg (fun u => ((γ⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ u) h3
      simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec] using h4.symm

end SheetDecomposition
end
end

