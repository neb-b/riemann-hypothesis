module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.AddMulSelfEqOfOrthogonalIdempotents
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

def Cx (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) (x : Matrix (Fin N) (Fin N) k) : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
  Algebra.adjoin k (insert x (Z : Set (Matrix (Fin N) (Fin N) k)))

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {x : Matrix (Fin N) (Fin N) k}

theorem cx_gens (hZ : CR Z) (hx : x ∈ Bz Z) :
    ∀ a ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
  intro a ha b hb
  rcases Set.mem_insert_iff.1 ha with h1 | h1
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h1, h2]
    · rw [h1]
      exact (hx b h2).symm
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h2]
      exact hx a h1
    · exact hZ.1 a h1 b h2

theorem cx_comm (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ a ∈ Cx Z x, ∀ b ∈ Cx Z x, a * b = b * a := by
  intro a ha b hb
  have key := cx_gens hZ hx
  have h : Commute a b := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
    intro c hc
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
    intro d hd
    exact key c hc d hd
  exact h.eq

theorem z_le_cx : Z ≤ Cx Z x := fun _ h => Algebra.subset_adjoin (Set.mem_insert_of_mem _ h)

theorem x_mem_cx : x ∈ Cx Z x := Algebra.subset_adjoin (Set.mem_insert _ _)

theorem pe_mem {d : ℕ} {c : Fin d → Matrix (Fin N) (Fin N) k} (hc : ∀ l, c l ∈ Z) : pe c x ∈ Cx Z x :=
  Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (z_le_cx (hc l)) (Subalgebra.pow_mem _ x_mem_cx _)

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransferAlt
section
noncomputable section

open Matrix Polynomial PositivityTheory.PfBern.Frob

namespace PositivityTheory.RgUd.TP.Desc.Piece.Tr

def DoubleTransfer : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H₁ H₂ : Subgroup G) [LocallyCompactSpace H₁] [LocallyCompactSpace H₂], IsClosed (H₁ : Set G) →
    IsClosed (H₂ : Set G) → IsUnimod G → IsUnimod H₁ → IsUnimod H₂ →
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
      [MulAction G X] [ContinuousSMul G X] (p₁ : X → G ⧸ H₁) (p₂ : X → G ⧸ H₂), Continuous p₁ → Continuous p₂ →
      ∀ (hp₁ : ∀ (g : G) (x : X), p₁ (g • x) = g • p₁ x) (hp₂ : ∀ (g : G) (x : X), p₂ (g • x) = g • p₂ x)
        (C : Set X), IsClosed C → (∀ g : G, ∀ x ∈ C, g • x ∈ C) →
        (∀ E ∈ eqvF hp₂ ((1 : G →* ℂˣ).comp H₂.subtype), SupportedIn E (Subtype.val ⁻¹' C)) →
        ∀ E ∈ eqvF hp₁ ((1 : G →* ℂˣ).comp H₁.subtype), SupportedIn E (Subtype.val ⁻¹' C)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def OrbHom : Prop :=
  ∀ (N : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A], IsReduced A →
    ∀ ρ ρ' : A →ₐ[k] Matrix (Fin N) (Fin N) k, (∀ e : A, IsIdempotentElem e → (ρ e).rank = (ρ' e).rank) →
      ∃ g : GL (Fin N) k, ∀ a, ρ' a = g.val * ρ a * g⁻¹.val

def OrbClosed : Prop :=
  ∀ (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A], IsReduced A →
    ∀ (b : Fin r → A), Submodule.span k (Set.range b) = ⊤ → ∀ ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k,
      IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val}

end PositivityTheory.RgUd.TP.Desc.Piece.Tr
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsClosedRank
section
noncomputable section

open Matrix Polynomial Topology

set_option linter.unusedSectionVars false

namespace PositivityTheory.RgUd.TP.Desc.Piece.PTop

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem rank_eq_near {e0 : Matrix (Fin N) (Fin N) k} (h0 : IsIdempotentElem e0) :
    ∃ U ∈ 𝓝 e0, ∀ e ∈ U, IsIdempotentElem e → e.rank = e0.rank := by
  refine ⟨{e | (e * e0 + (1 - e) * (1 - e0)).det ≠ 0}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact isOpen_ne_fun (Continuous.matrix_det ((continuous_id.mul continuous_const).add
        ((continuous_const.sub continuous_id).mul continuous_const))) continuous_const
    · show (e0 * e0 + (1 - e0) * (1 - e0)).det ≠ 0
      have h1 : (1 - e0) * (1 - e0) = 1 - e0 := h0.one_sub.eq
      rw [h0.eq, h1, add_sub_cancel, det_one]
      exact one_ne_zero
  · intro e he hide
    have hu : IsUnit (e * e0 + (1 - e) * (1 - e0)).det := isUnit_iff_ne_zero.2 he
    have key : e * (e * e0 + (1 - e) * (1 - e0)) = (e * e0 + (1 - e) * (1 - e0)) * e0 := by
      have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hide.eq, sub_self]
      have h2 : (1 - e0) * e0 = 0 := by rw [sub_mul, one_mul, h0.eq, sub_self]
      rw [mul_add, ← mul_assoc, ← mul_assoc, hide.eq, h1, zero_mul, add_zero, add_mul,
        mul_assoc (1 - e), h2, mul_zero, add_zero, mul_assoc, h0.eq]
    rw [← Matrix.rank_mul_eq_left_of_isUnit_det _ e hu, key, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]

theorem isClosed_rank {X : Type} [TopologicalSpace X] {F : Set X} (hF : IsClosed F)
    {f : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hi : ∀ x ∈ F, IsIdempotentElem (f x)) (r : ℕ) :
    IsClosed {x | x ∈ F ∧ (f x).rank = r} := by
  apply isClosed_of_closure_subset
  intro x hx
  have hxF : x ∈ F := hF.closure_subset (closure_mono (by exact fun y hy => hy.1) hx)
  obtain ⟨U, hU, hUe⟩ := rank_eq_near (hi x hxF)
  obtain ⟨y, hyU, hyF, hyr⟩ := mem_closure_iff_nhds.1 hx _ (hf.continuousAt.preimage_mem_nhds hU)
  exact ⟨hxF, (hUe _ hyU (hi y hyF)).symm.trans hyr⟩

theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) : IsClosed (Bz Z) := by
  have h : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin N) (Fin N) k | a * x = x * a} := by
    ext x
    simp [Bz]
  rw [h]
  exact isClosed_biInter (fun a _ => isClosed_eq (continuous_const.mul continuous_id)
    (continuous_id.mul continuous_const))

theorem continuous_pe {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k) : Continuous (pe c) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_pow _)

theorem pe_conj {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k)
    (hc : ∀ l, c l ∈ Z) {g : GL (Fin N) k} (hg : g ∈ Gz Z) (x : Matrix (Fin N) (Fin N) k) :
    pe c (g.val * x * g⁻¹.val) = g.val * pe c x * g⁻¹.val := by
  unfold pe
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Units.conj_pow]
  simp only [mul_assoc]
  rw [← mul_assoc (c l), hg _ (hc l), mul_assoc]

theorem aeval_conj (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (χ : k[X]) :
    aeval (g.val * x * g⁻¹.val) χ = g.val * aeval x χ * g⁻¹.val := by
  induction χ using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add (f := _), hp, hr, mul_add, add_mul]
  | monomial n a =>
    simp only [aeval_monomial, Units.conj_pow, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

theorem rank_conj (g : GL (Fin N) k) (e : Matrix (Fin N) (Fin N) k) : (g.val * e * g⁻¹.val).rank = e.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (g⁻¹).isUnit),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]

variable (k) in
theorem pieceTop : PieceTop k := by
  intro N q Z hZ χ D τ
  have hF : IsClosed {x : Matrix (Fin N) (Fin N) k | x ∈ Bz Z ∧ aeval x χ = 0} :=
    (isClosed_Bz Z).inter (isClosed_eq (Polynomial.continuous_aeval χ) continuous_const)
  have hft : ∀ t : Fin D.m, Continuous fun x : Matrix (Fin N) (Fin N) k =>
      ∑ j : Fin D.r, D.κ t j • pe (D.a j) x :=
    fun t => continuous_finsetSum _
      (fun j _ => (continuous_const_smul (D.κ t j)).comp (continuous_pe (D.a j)))
  have hidem : ∀ t : Fin D.m, ∀ x ∈ {x : Matrix (Fin N) (Fin N) k | x ∈ Bz Z ∧ aeval x χ = 0},
      IsIdempotentElem (∑ j : Fin D.r, D.κ t j • pe (D.a j) x) :=
    fun t x hx => (D.spec x hx.1 hx.2).2.2.2.2.2.2.2.2.1 t
  refine ⟨?_, ?_, ?_⟩
  · have h : piece D τ = {x | x ∈ Bz Z ∧ aeval x χ = 0} ∩ ⋂ t, {x | x ∈ {x : Matrix (Fin N) (Fin N) k |
        x ∈ Bz Z ∧ aeval x χ = 0} ∧ (∑ j : Fin D.r, D.κ t j • pe (D.a j) x).rank = τ t} := by
      ext x
      simp only [piece, typ, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, funext_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun t => ⟨⟨h1, h2⟩, h3 t⟩⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, fun t => (h3 t).2⟩
    rw [h]
    exact hF.inter (isClosed_iInter fun t => isClosed_rank hF (hft t) (hidem t) (τ t))
  · rintro g hg x ⟨hxB, hxa, hxt⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have hga : a * g.val = g.val * a := hg a ha
      have hgi : a * (g⁻¹).val = (g⁻¹).val * a := by
        calc a * (g⁻¹).val = (g⁻¹).val * (g.val * a) * (g⁻¹).val := by rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = (g⁻¹).val * (a * g.val) * (g⁻¹).val := by rw [hga]
          _ = (g⁻¹).val * a := by rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      calc a * (g.val * x * (g⁻¹).val) = g.val * (a * x) * (g⁻¹).val := by simp only [← mul_assoc, hga]
        _ = g.val * (x * a) * (g⁻¹).val := by rw [hxB a ha]
        _ = g.val * x * (g⁻¹).val * a := by simp only [mul_assoc, hgi]
    · rw [aeval_conj, hxa, mul_zero, zero_mul]
    · rw [← hxt]
      funext t
      simp only [typ]
      have h : ∑ j, D.κ t j • pe (D.a j) (g.val * x * (g⁻¹).val) = g.val * (∑ j, D.κ t j • pe (D.a j) x) * (g⁻¹).val := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [pe_conj (D.a j) (D.ha j) hg, mul_smul_comm, smul_mul_assoc]
      rw [h, rank_conj]
  · intro x hx
    obtain ⟨hxB, hxa, -⟩ := hx
    have sp := D.spec x hxB hxa
    simp only at sp
    obtain ⟨hmul, hone, hcomm, -, -, hred, -⟩ := sp
    have hspan_mul : ∀ a b, a ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) →
        b ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) →
        a * b ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) := by
      intro a b ha hb
      have h1 := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨j', rfl⟩, rfl⟩
      show pe (D.a j) x * pe (D.a j') x ∈ _
      rw [hmul j j']
      exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩))
    have h1mem : (1 : Matrix (Fin N) (Fin N) k) ∈ Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x) := by
      rw [← hone]
      exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    have hle : Sx D x ≤ (Submodule.span k (Set.range fun j : Fin D.r => pe (D.a j) x)).toSubalgebra
        h1mem hspan_mul := by
      apply Algebra.adjoin_le
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
    refine ⟨?_, ⟨fun y hy => ?_⟩⟩
    · intro a ha b hb
      have ha' : a ∈ Algebra.adjoin k (Set.range fun j : Fin D.r => pe (D.a j) x) := ha
      have hb' : b ∈ Algebra.adjoin k (Set.range fun j : Fin D.r => pe (D.a j) x) := hb
      have hgen : ∀ u ∈ Set.range (fun j : Fin D.r => pe (D.a j) x), Commute u b := by
        intro u hu
        refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb' ?_
        rintro _ ⟨j', rfl⟩
        obtain ⟨j, rfl⟩ := hu
        exact hcomm j j'
      exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha' (fun u hu => (hgen u hu).symm)).symm.eq
    · apply Subtype.ext
      exact hred _ (hle y.2) (hy.map (Sx D x).val)

end PositivityTheory.RgUd.TP.Desc.Piece.PTop
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RootsFinite
section
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

open Polynomial PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_pow' {N : ℕ} (g : GL (Fin N) k) (y : Matrix (Fin N) (Fin N) k) (n : ℕ) :
    (g.val * y * g⁻¹.val) ^ n = g.val * y ^ n * g⁻¹.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem roots_finite {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]} (hχ : χ ≠ 0) :
    {c : Matrix (Fin N) (Fin N) k | c ∈ Z ∧ aeval c χ = 0}.Finite := by
  letI : CommRing Z := { (inferInstance : Ring ↥Z) with mul_comm := fun a b => Subtype.ext (hZ.1 a a.2 b b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  have hT : {c : Z | aeval c χ = 0}.Finite := by
    refine Set.Finite.of_finite_image ?_ (IsArtinianRing.equivPi Z).injective.injOn
    refine (Set.Finite.pi (t := fun I : MaximalSpectrum Z => χ.rootSet (Z ⧸ I.asIdeal))
      fun I => χ.rootSet_finite _).subset ?_
    rintro _ ⟨c, hc, rfl⟩
    refine Set.mem_univ_pi.2 fun I => ?_
    rw [mem_rootSet_of_ne hχ, IsArtinianRing.equivPi_apply]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I.asIdeal) c χ
    rw [show aeval c χ = 0 from hc, map_zero] at h
    exact h
  refine (hT.image Subtype.val).subset ?_
  rintro c ⟨hc, h0⟩
  refine ⟨⟨c, hc⟩, ?_, rfl⟩
  show aeval (⟨c, hc⟩ : Z) χ = 0
  exact Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact h0)

theorem root_of_nil {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]}
    {x c : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hc : c ∈ Z) (hχx : aeval x χ = 0)
    (hn : IsNilpotent (x - c)) : aeval c χ = 0 := by
  have hxc : x * c = c * x := (hx c hc).symm
  have hcomm : ∀ a ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxc
    · exact hxc.symm
    · rfl
  let A := Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin k (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing A := { (inferInstance : Ring A) with mul_comm := fun a b => mul_comm' a b }
  let xa : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  let ca : A := ⟨c, Algebra.subset_adjoin (by simp)⟩
  have hna : IsNilpotent (xa - ca) := (IsNilpotent.map_iff (f := A.val) Subtype.val_injective).1 hn
  have h1 := isNilpotent_aeval_sub_of_isNilpotent_sub χ hna
  have h2 : aeval xa χ = 0 := Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact hχx)
  have h3 : IsNilpotent (aeval ca χ) := by simpa [h2] using h1.neg
  have h4 : IsNilpotent (aeval c χ) := by
    have := h3.map A.val
    rwa [← Polynomial.aeval_algHom_apply] at this
  let c' : Z := ⟨c, hc⟩
  have h5 : IsNilpotent (aeval c' χ) := by
    refine (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 ?_
    rw [← Polynomial.aeval_algHom_apply]
    exact h4
  have h6 : aeval c' χ = 0 := by
    haveI : IsReduced Z := hZ.2
    exact h5.eq_zero
  have h7 := congrArg Subtype.val h6
  rwa [Polynomial.aeval_subalgebra_coe] at h7


variable (k) in
theorem pieceGood_of (hF : PositivityTheory.PfBern.Frob.FrobeniusReciprocity) (hS : Sect k) (hP : PieceTop k) (hD : Dich k)
    (hT : Transfer k) : PieceGood k := by
  classical
  intro p _ _ hU N q Z hZ hq hR hB χ
  by_cases hχ : χ.Monic ∧ χ.natDegree = N
  swap
  · refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun x _ hc => ?_⟩, fun i => i.elim0⟩
    exact (hχ ⟨hc ▸ x.charpoly_monic, by rw [← hc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩).elim
  obtain ⟨D⟩ := hS p N q Z hZ hq hR hB χ hχ.1 hχ.2
  have hfin := roots_finite hZ hχ.1.ne_zero
  have hrt : ∀ j : Fin hfin.toFinset.card, (hfin.toFinset.equivFin.symm j).1 ∈ Z ∧
      aeval (hfin.toFinset.equivFin.symm j).1 χ = 0 := fun j => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm j).2
  let rt : Fin hfin.toFinset.card → Matrix (Fin N) (Fin N) k := fun j => (hfin.toFinset.equivFin.symm j).1
  have rt_inj : Function.Injective rt := fun j j' h => hfin.toFinset.equivFin.symm.injective (Subtype.ext h)
  have hred : ∀ c ∈ Z, IsNilpotent c → c = 0 := fun c hc hn => by
    have h : IsNilpotent (⟨c, hc⟩ : Z) := (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 hn
    haveI : IsReduced Z := hZ.2
    exact congrArg Subtype.val h.eq_zero
  have hcz : ∀ c ∈ Z, ∀ x ∈ Bz Z, x - c ∈ Bz Z := fun c hc x hx a ha => by
    rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
  let e := (finFunctionFinEquiv (m := N + 1) (n := D.m)).symm
  let τ : Fin ((N + 1) ^ D.m) → Fin D.m → ℕ := fun i t => (e i t : ℕ)
  have τ_inj : Function.Injective τ := fun i j h => e.injective (funext fun t => Fin.ext (congrFun h t))
  let bad : Fin ((N + 1) ^ D.m) → Prop := fun i => ∃ x₀ ∈ piece D (τ i), mu (Sx D x₀) < mu Z
  let G : Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card) → Set (Matrix (Fin N) (Fin N) k) := fun is =>
    if bad is.1 then (if is.2 = none then piece D (τ is.1) else ∅)
    else is.2.elim ∅ (fun j => {x | x ∈ piece D (τ is.1) ∧ (x - rt j) ^ q = 0})
  have hsub : ∀ is x, x ∈ G is → x ∈ piece D (τ is.1) := by
    rintro ⟨i, s⟩ x hx
    simp only [G] at hx
    split_ifs at hx
    · exact hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j => exact hx.1
  have huniq : ∀ is js x, x ∈ G is → x ∈ G js → is = js := by
    rintro ⟨i, s⟩ ⟨j, t⟩ x hx hy
    have hij : i = j := τ_inj ((hsub _ x hx).2.2.symm.trans (hsub _ x hy).2.2)
    subst hij
    have hxB : x ∈ Bz Z := (hsub _ x hx).1
    simp only [G] at hx hy
    by_cases hb : bad i
    · rw [if_pos hb] at hx hy
      split_ifs at hx hy with h1 h2
      · rw [h1, h2]
      · simp at hy
      · simp at hx
      · simp at hx
    · rw [if_neg hb] at hx hy
      cases s with
      | none => simp at hx
      | some a =>
        cases t with
        | none => simp at hy
        | some b =>
          have ha : IsNilpotent (x - rt a) := ⟨q, hx.2⟩
          have hb' : IsNilpotent (x - rt b) := ⟨q, hy.2⟩
          have hca : Commute (rt a) x := hxB _ (hrt a).1
          have hcb : Commute (rt b) x := hxB _ (hrt b).1
          have hab : Commute (rt b) (rt a) := hZ.1 _ (hrt b).1 _ (hrt a).1
          have hcomm : Commute (x - rt b) (x - rt a) :=
            ((Commute.refl x).sub_right hca.symm).sub_left (hcb.sub_right hab)
          have hn : IsNilpotent (rt a - rt b) := by
            have := hcomm.isNilpotent_sub hb' ha
            rwa [sub_sub_sub_cancel_left] at this
          have h0 := hred _ (Z.sub_mem (hrt a).1 (hrt b).1) hn
          rw [rt_inj (sub_eq_zero.1 h0)]
  have hclosed : ∀ is, IsClosed (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs
    · exact (hP N q Z hZ χ D (τ i)).1
    · exact isClosed_empty
    · cases s with
      | none => exact isClosed_empty
      | some j =>
        exact (hP N q Z hZ χ D (τ i)).1.inter
          (isClosed_eq ((continuous_id.sub continuous_const).pow q) continuous_const)
  have hinvar : ∀ is, ∀ g ∈ Gz Z, ∀ x ∈ G is, g.val * x * g⁻¹.val ∈ G is := by
    rintro ⟨i, s⟩ g hg x hx
    have hP2 := (hP N q Z hZ χ D (τ i)).2.1 g hg
    simp only [G] at hx ⊢
    split_ifs at hx ⊢
    · exact hP2 x hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j =>
        refine ⟨hP2 x hx.1, ?_⟩
        have e1 : g.val * x * g⁻¹.val - rt j = g.val * (x - rt j) * g⁻¹.val := by
          rw [mul_sub, sub_mul, ← hg (rt j) (hrt j).1, mul_assoc (rt j), Units.mul_inv, mul_one]
        rw [e1, conj_pow', hx.2, mul_zero, zero_mul]
  have hcover : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ is, x ∈ G is := by
    intro x hx hc
    have hle : ∀ t, typ D x t < N + 1 := fun t =>
      Nat.lt_succ_of_le ((Matrix.rank_le_width _).trans (by simp))
    let i := e.symm fun t => ⟨typ D x t, hle t⟩
    have hxp : x ∈ piece D (τ i) :=
      ⟨hx, by rw [← hc]; exact Matrix.aeval_self_charpoly x, by funext t; simp [τ, i]⟩
    by_cases hb : bad i
    · refine ⟨(i, none), ?_⟩
      simp only [G, if_pos hb, if_true]
      exact hxp
    · rcases hD N q Z hZ χ D (τ i) x hxp with h | ⟨c, hc, hn⟩
      · exact (hb ⟨x, hxp, h⟩).elim
      · have hroot : aeval c χ = 0 := root_of_nil hZ hx hc hxp.2.1 hn
        have hmem : c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨hc, hroot⟩
        refine ⟨(i, some (hfin.toFinset.equivFin ⟨c, hmem⟩)), ?_⟩
        have hrtc : rt (hfin.toFinset.equivFin ⟨c, hmem⟩) = c := by simp [rt]
        simp only [G, if_neg hb, Option.elim_some]
        refine ⟨hxp, ?_⟩
        rw [hrtc]
        exact hB _ (hcz c hc x hx) hn
  have hgood : ∀ is, Good Z (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs with h1
    · obtain ⟨x₀, hx₀, hlt⟩ := h1
      exact Or.inr ⟨N, Sx D x₀, (hP N q Z hZ χ D (τ i)).2.2 x₀ hx₀, hlt, hT hF p hU N q Z hZ χ D (τ i) x₀ hx₀⟩
    · exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
    · cases s with
      | none => exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
      | some j => exact Or.inl ⟨rt j, (hrt j).1, fun x hx => ⟨q, hx.2⟩⟩
  let eqv := Fintype.equivFin (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card))
  refine ⟨Fintype.card (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card)), fun i => G (eqv.symm i),
    ⟨fun i => ⟨hclosed _, fun x hx => (hsub _ x hx).1, hinvar _⟩,
      fun i j hij => Set.disjoint_left.2 fun x h1 h2 => hij (eqv.symm.injective (huniq _ _ x h1 h2)),
      fun x hx hc => ?_⟩, fun i => hgood _⟩
  obtain ⟨is, his⟩ := hcover x hx hc
  exact ⟨eqv is, by simpa using his⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

end
end

