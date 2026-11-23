module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Pieces
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbB

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransfer
section
noncomputable section

open PositivityTheory.PfBern.Frob PositivityTheory.RgUd.TP.Desc.Piece.Tr

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrDbl

theorem doubleTransfer : FrobeniusReciprocity → DoubleTransfer := by
  intro hF G _ _ _ _ _ _ _ _ _ H₁ H₂ _ _ hH₁ hH₂ hG hU₁ hU₂ X _ _ _ _ _ _ p₁ p₂ hc₁ hc₂ hp₁ hp₂ C hC hCinv hE₂ E hE
  obtain ⟨Fr₁, hs₁, -⟩ := hF G H₁ hH₁ hG hU₁ X p₁ hc₁ hp₁ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  obtain ⟨Fr₂, hs₂, -⟩ := hF G H₂ hH₂ hG hU₂ X p₂ hc₂ hp₂ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  set ξ := Fr₁.symm ⟨E, hE⟩
  have h2 : SupportedIn (↑ξ) C := (hs₂ ξ C hC hCinv).2 (hE₂ _ (Fr₂ ξ).2)
  have h1 := (hs₁ ξ C hC hCinv).1 h2
  simpa [ξ] using h1

end PositivityTheory.RgUd.TP.Desc.Piece.TrDbl
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsPretransitiveActO
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem tdM : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := by
  haveI := (tdk : TotallyDisconnectedSpace k)
  exact (inferInstance : TotallyDisconnectedSpace (Fin N → Fin N → k))

theorem comm_span_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) (y : Matrix (Fin N) (Fin N) k) :
    (∀ a ∈ S, a * y = y * a) ↔ ∀ i, b i * y = y * b i := by
  have hmem : ∀ a, a ∈ S ↔ a ∈ Submodule.span k (Set.range b) := fun a => by
    rw [← hb]; rfl
  constructor
  · exact fun h i => h _ ((hmem _).2 (Submodule.subset_span ⟨i, rfl⟩))
  · intro h a ha
    have key : ∀ a ∈ Submodule.span k (Set.range b), a * y = y * a := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
      | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
    exact key a ((hmem a).1 ha)

theorem cj_eq_self_iff (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g x = x ↔ x * g.val = g.val * x := by
  unfold cj
  constructor
  · intro h
    calc x * g.val = (↑g * x * ↑g⁻¹) * g.val := by rw [h]
      _ = g.val * x := by simp [mul_assoc]
  · intro h
    rw [← h, mul_assoc, Units.mul_inv, mul_one]

theorem mem_GzS_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) (g : GL (Fin N) k) :
    g ∈ GzS S ↔ ∀ i, cj g (b i) = b i := by
  exact (show g ∈ GzS S ↔ ∀ a ∈ S, a * g.val = g.val * a from Iff.rfl).trans
    ((comm_span_iff hb _).trans (forall_congr' fun i => (cj_eq_self_iff g (b i)).symm))

def Orb {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
  {w | ∃ g : GL (Fin N) k, ∀ i, w i = cj g (b i)}

theorem self_mem_orb {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : b ∈ Orb b :=
  ⟨1, fun i => (cj_one _).symm⟩

theorem cj_mem_orb {r : ℕ} {b w : Fin r → Matrix (Fin N) (Fin N) k} (hw : w ∈ Orb b) (g : GL (Fin N) k) :
    (fun i => cj g (w i)) ∈ Orb b := by
  obtain ⟨h, hh⟩ := hw
  exact ⟨g * h, fun i => by show cj g (w i) = _; rw [hh, cj_mul]⟩

abbrev cr_commRing {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S) : CommRing S :=
  { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (hS.1 a a.2 b b.2) }

theorem span_top_of {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    Submodule.span k (Set.range fun i => (⟨b i, by
      show b i ∈ S.toSubmodule; rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : S)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : Matrix (Fin N) (Fin N) k) ∈ Submodule.span k (Set.range b) := by
    rw [← hb]
    exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨c, ?_⟩
  apply Subtype.ext
  rw [← hc]
  simp

theorem isClosed_orb (hO : OrbClosed k) {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S)
    {b : Fin r → Matrix (Fin N) (Fin N) k} (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    IsClosed (Orb b) := by
  letI : CommRing S := cr_commRing hS
  haveI : IsReduced S := hS.2
  exact hO N r S hS.2 _ (span_top_of hb) S.val

def actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : MulAction (GL (Fin N) k) (Orb b) where
  smul g w := ⟨fun i => cj g (w.1 i), cj_mem_orb w.2 g⟩
  one_smul w := Subtype.ext (funext fun i => cj_one _)
  mul_smul g h w := Subtype.ext (funext fun i => cj_mul g h _)

theorem continuousSMul_actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) :
    @ContinuousSMul (GL (Fin N) k) (Orb b) (actO b).toSMul _ _ := by
  letI := actO b
  refine ⟨?_⟩
  show Continuous (fun p : GL (Fin N) k × Orb b => (⟨fun i => cj p.1 (p.2.1 i), cj_mem_orb p.2.2 p.1⟩ : Orb b))
  have hc : ∀ i : Fin r, Continuous (fun p : GL (Fin N) k × Orb b => cj p.1 (p.2.1 i)) := by
    intro i
    have h1 : Continuous (fun p : GL (Fin N) k × Orb b => p.2.1 i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have h2 : Continuous (fun p : GL (Fin N) k × Orb b => (p.1, p.2.1 i)) := continuous_fst.prodMk h1
    exact (continuous_cj (n := N)).comp h2
  exact Continuous.subtype_mk (continuous_pi hc) _

theorem isPretransitive_actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) :
    @MulAction.IsPretransitive (GL (Fin N) k) (Orb b) (actO b).toSMul := by
  letI := actO b
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := x.2
  obtain ⟨h, hh⟩ := y.2
  refine ⟨h * g⁻¹, Subtype.ext (funext fun i => ?_)⟩
  show cj (h * g⁻¹) (x.1 i) = y.1 i
  rw [hg i, hh i, ← cj_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_orb_homeo (hO : OrbClosed k) {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S)
    {b : Fin r → Matrix (Fin N) (Fin N) k} (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    ∃ e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b, ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → Matrix (Fin N) (Fin N) k) =
      fun i => cj g (b i) := by
  letI := actO b
  haveI := continuousSMul_actO b
  haveI := isPretransitive_actO b
  haveI : LocallyCompactSpace (Orb b) := (isClosed_orb hO hS hb).locallyCompactSpace
  obtain ⟨e, he⟩ := exists_quotient_homeo (G := GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b)
  have hst : MulAction.stabilizer (GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b) = GzS S := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_GzS_iff hb]
    constructor
    · intro h i
      exact congrFun (congrArg Subtype.val h) i
    · intro h
      exact Subtype.ext (funext h)
  have key : ∀ H : Subgroup (GL (Fin N) k),
      MulAction.stabilizer (GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b) = H →
      ∃ e : GL (Fin N) k ⧸ H ≃ₜ Orb b, ∀ g : GL (Fin N) k,
        ((e g : Orb b) : Fin r → Matrix (Fin N) (Fin N) k) = fun i => cj g (b i) := by
    rintro H rfl
    exact ⟨e, fun g => by rw [he g]; rfl⟩
  exact key _ hst

theorem rank_add_of_orth {e f : Matrix (Fin N) (Fin N) k} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) : (e + f).rank = e.rank + f.rank := by
  have hE : (e + f) * e = e := by rw [add_mul, he.eq, hfe, add_zero]
  have hF : (e + f) * f = f := by rw [add_mul, hef, hf.eq, zero_add]
  have hsup : LinearMap.range (e + f).mulVecLin =
      LinearMap.range e.mulVecLin ⊔ LinearMap.range f.mulVecLin := by
    apply le_antisymm
    · rw [Matrix.mulVecLin_add]
      exact LinearMap.range_add_le _ _
    · refine sup_le ?_ ?_
      · conv_lhs => rw [← hE]
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _
      · conv_lhs => rw [← hF]
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _
  have hinf : LinearMap.range e.mulVecLin ⊓ LinearMap.range f.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_inf, LinearMap.mem_range, Matrix.mulVecLin_apply] at hx
    obtain ⟨⟨u, rfl⟩, ⟨w, hw⟩⟩ := hx
    rw [Submodule.mem_bot]
    have hu : e *ᵥ u = e *ᵥ (e *ᵥ u) := by rw [Matrix.mulVec_mulVec, he.eq]
    rw [hu, ← hw, Matrix.mulVec_mulVec, hef, Matrix.zero_mulVec]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e.mulVecLin) (LinearMap.range f.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  unfold Matrix.rank
  exact h

theorem rank_sum_orth {ι : Type*} [DecidableEq ι] (e : ι → Matrix (Fin N) (Fin N) k) (he : ∀ t, IsIdempotentElem (e t))
    (ho : ∀ t t', t ≠ t' → e t * e t' = 0) (T : Finset ι) :
    IsIdempotentElem (∑ t ∈ T, e t) ∧ (∑ t ∈ T, e t).rank = ∑ t ∈ T, (e t).rank := by
  refine Finset.induction_on T ?_ ?_
  · refine ⟨?_, ?_⟩ <;> simp [IsIdempotentElem, Matrix.rank_zero]
  · intro a s ha ih
    have h1 : e a * ∑ t ∈ s, e t = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun t ht => ho a t (fun h => ha (by rw [h]; exact ht))
    have h2 : (∑ t ∈ s, e t) * e a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun t ht => ho t a (fun h => ha (by rw [← h]; exact ht))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(he a).add ih.1 (by rw [h1, h2, add_zero]), by rw [rank_add_of_orth (he a) ih.1 h1 h2, ih.2]⟩

theorem cr_bot : CR (⊥ : Subalgebra k (Matrix (Fin N) (Fin N) k)) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha
    exact Algebra.commutes c b
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨n, hn⟩ := hx
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 x.2
    have hn' : (x : Matrix (Fin N) (Fin N) k) ^ n = 0 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [← hc, ← map_pow] at hn'
    by_cases h0 : c = 0
    · apply Subtype.ext
      rw [← hc, h0, map_zero]
      rfl
    · have h1 : (1 : Matrix (Fin N) (Fin N) k) = 0 := by
        have hcn : c ^ n ≠ 0 := pow_ne_zero _ h0
        calc (1 : Matrix (Fin N) (Fin N) k) = algebraMap k _ ((c ^ n)⁻¹ * c ^ n) := by
              rw [inv_mul_cancel₀ hcn, map_one]
          _ = 0 := by rw [map_mul, hn', mul_zero]
      apply Subtype.ext
      show (x : Matrix (Fin N) (Fin N) k) = 0
      rw [← mul_one (x : Matrix (Fin N) (Fin N) k), h1, mul_zero]

def glEquivBot : GL (Fin N) k ≃ₜ* GzS (⊥ : Subalgebra k (Matrix (Fin N) (Fin N) k)) where
  toFun g := ⟨g, fun a ha => by obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha; exact Algebra.commutes c g.val⟩
  invFun g := g.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_id _
  continuous_invFun := continuous_subtype_val

theorem isUnimod_GL (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : PositivityTheory.PfBern.Frob.IsUnimod (GL (Fin N) k) :=
  isUnimod_of_equiv glEquivBot (hU N ⊥ cr_bot)

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OrbClosed
section
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbHom : Tr.OrbHom k := fun N A _ _ _ hA ρ ρ' h => orbHom_gen k N A hA ρ ρ' h

theorem orbClosed : Tr.OrbClosed k := fun N r A _ _ _ hA b hb ρ₀ => orbClosed_gen N r A hA b hb ρ₀

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.SxToSub
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k}

def Nx (x : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Cx Z x).toSubmodule.map (LinearMap.mulLeft k (pe D.b x))

theorem s_mem (j : Fin D.r) : pe (D.a j) x ∈ Sx D x := Algebra.subset_adjoin ⟨j, rfl⟩

theorem sx_le : Sx D x ≤ Cx Z x := Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact pe_mem (D.ha j))

theorem sx_toSub (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    (Sx D x).toSubmodule = Submodule.span k (Set.range fun j => pe (D.a j) x) := by
  obtain ⟨h1, h2, -⟩ := D.spec x hx hχ
  apply le_antisymm
  · let P : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
      (Submodule.span k (Set.range fun j => pe (D.a j) x)).toSubalgebra ?one ?mul
    · have hle : Sx D x ≤ P := by
        refine Algebra.adjoin_le ?_
        intro y hy
        exact Submodule.subset_span hy
      intro y hy
      exact hle hy
    case one =>
      rw [← h2]
      refine Submodule.sum_mem _ ?_
      intro j _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    case mul =>
      intro a b ha hb
      have hab : a * b ∈ Submodule.span k (Set.range fun j => pe (D.a j) x) *
          Submodule.span k (Set.range fun j => pe (D.a j) x) := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at hab
      refine (Submodule.span_le.2 ?_) hab
      rintro _ ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩
      have e := h1 i j
      simp only at e ⊢
      rw [e]
      refine Submodule.sum_mem _ ?_
      intro t _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · refine Submodule.span_le.2 ?_
    intro y hy
    exact Algebra.subset_adjoin hy

theorem sx_nil (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ y ∈ Sx D x, IsNilpotent y → y = 0 := by
  obtain ⟨-, -, -, -, -, hred, -⟩ := D.spec x hx hχ
  intro y hy hn
  have : y ∈ (Sx D x).toSubmodule := hy
  rw [sx_toSub D hx hχ] at this
  exact hred y this hn

theorem sx_cr (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : CR (Sx D x) := by
  refine ⟨fun a ha b hb => cx_comm hZ hx a (sx_le D ha) b (sx_le D hb), ⟨fun y hy => ?_⟩⟩
  exact Subtype.ext (sx_nil D hx hχ y.1 y.2 (hy.map (Sx D x).val))

theorem nx_le : Nx D x ≤ (Cx Z x).toSubmodule := by
  refine Submodule.map_le_iff_le_comap.2 ?_
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
  exact (Cx Z x).mul_mem (pe_mem D.hb) hy

theorem nx_nil (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ n ∈ Nx D x, IsNilpotent n := by
  obtain ⟨-, -, -, -, hεq, -⟩ := D.spec x hx hχ
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨q, ?_⟩
  simp only [LinearMap.mulLeft_apply]
  rw [(Commute.mul_pow (cx_comm hZ hx _ (pe_mem D.hb) c hc) q), hεq, zero_mul]

theorem nx_mul (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ c ∈ Cx Z x, ∀ n ∈ Nx D x, c * n ∈ Nx D x := by
  intro c hc n hn
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨c * y, (Cx Z x).mul_mem hc hy, ?_⟩
  rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc,
    cx_comm hZ hx _ hc _ (pe_mem D.hb)]

theorem re_mem (hZ : CR Z) (hx : x ∈ Bz Z) (γ' : Fin D.d → Fin D.r → k) :
    re γ' (fun j => pe (D.a j) x) (pe D.b x) ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  simp only [re]
  refine Submodule.sum_mem _ ?_
  intro l _
  refine Submodule.sum_mem _ ?_
  intro j _
  refine Submodule.smul_mem _ _ ?_
  obtain h | ⟨m, hm⟩ : (l : ℕ) = 0 ∨ ∃ m, (l : ℕ) = m + 1 := by
    rcases (l : ℕ) with _ | m
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [h, pow_zero, mul_one]
    exact Submodule.mem_sup_left (s_mem D j)
  · have hs : pe (D.a j) x ∈ Cx Z x := pe_mem (D.ha j)
    have he : pe D.b x ∈ Cx Z x := pe_mem D.hb
    rw [hm, pow_succ', ← mul_assoc, cx_comm hZ hx _ hs _ he, mul_assoc]
    refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨pe (D.a j) x * pe D.b x ^ m, ?_, ?_⟩)
    · exact (Cx Z x).mul_mem hs ((Cx Z x).pow_mem he m)
    · rw [LinearMap.mulLeft_apply]

theorem z_le (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : Z.toSubmodule ≤ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, hz, -⟩ := D.spec x hx hχ
  rw [D.hz]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [hz i]
  exact re_mem D hZ hx (D.γ i)

theorem x_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : x ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, -, hxb, -⟩ := D.spec x hx hχ
  have := re_mem D hZ hx D.β
  rwa [← hxb] at this

theorem idem_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ Z)
    (hfi : IsIdempotentElem f) : f ∈ Sx D x := by
  have hfm : f ∈ (Sx D x).toSubmodule ⊔ Nx D x := z_le D hZ hx hχ hf
  obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.1 hfm
  have hsS : s ∈ Sx D x := hs
  have hsC : s ∈ Cx Z x := sx_le D hsS
  have hnC : n ∈ Cx Z x := nx_le D hn
  have hfC : f ∈ Cx Z x := z_le_cx hf
  have hnn : IsNilpotent n := nx_nil D hZ hx hχ n hn
  have cfn : Commute f n := cx_comm hZ hx f hfC n hnC
  have cfs : Commute f s := cx_comm hZ hx f hfC s hsC
  have hs_eq : s = f - n := by rw [← hsn]; abel
  have key : s * s - s = n * (n + 1 - 2 * f) := by
    have e : (f - n) * (f - n) - (f - n) - n * (n + 1 - 2 * f) = (f * f - f) + (n * f - f * n) := by
      noncomm_ring
    rw [hfi.eq, cfn.eq, sub_self, sub_self, add_zero, sub_eq_zero] at e
    rw [hs_eq]
    exact e
  have c2 : Commute n (2 * f) := by
    rw [two_mul]
    exact cfn.symm.add_right cfn.symm
  have cn2 : Commute n (n + 1 - 2 * f) :=
    ((Commute.refl n).add_right (Commute.one_right n)).sub_right c2
  have hnil : IsNilpotent (s * s - s) := by
    rw [key]
    exact Commute.isNilpotent_mul_right cn2 hnn
  have hz : s * s - s = 0 :=
    sx_nil D hx hχ _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hsS hsS) hsS) hnil
  have hsi : IsIdempotentElem s := sub_eq_zero.1 hz
  have hfs : f - s = n := by rw [← hsn]; abel
  have hfeq : f = s :=
    eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute hfi hsi (by rw [hfs]; exact hnn) cfs
  rw [hfeq]
  exact hsS

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

