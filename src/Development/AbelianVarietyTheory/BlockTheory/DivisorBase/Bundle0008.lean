module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

open Formalism.L2.DIV GlobalTheory.FinGL

variable {F : Type} [Field F] {r : ℕ}

abbrev Block (b : Fin r → ℕ) (c : ℕ) : Type := {a : Fin r // b a = c}

def blockMat (b : Fin r → ℕ) (c : ℕ) : Matrix (Block b c) (Block b c) F →* Matrix (Fin r) (Fin r) F where
  toFun g := Matrix.reindex (Equiv.sumCompl fun a => b a = c) (Equiv.sumCompl fun a => b a = c)
    (Matrix.fromBlocks g 0 0 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem blockMat_in (b : Fin r → ℕ) (c : ℕ) (g : Matrix (Block b c) (Block b c) F) (i j : Block b c) :
    blockMat b c g i.1 j.1 = g i j := by
  simp [blockMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) i.2,
    Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) j.2]

theorem blockMat_out (b : Fin r → ℕ) (c : ℕ) (g : Matrix (Block b c) (Block b c) F) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) : blockMat b c g i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · exact absurd ⟨hi, hj⟩ h
  · have : i ≠ j := fun e => hj (e ▸ hi)
    simp [blockMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, this]
  · have : i ≠ j := fun e => hi (e ▸ hj)
    simp [blockMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hj, this]
  · simp [blockMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, Matrix.one_apply]

def toBlock (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) :
    Matrix (Fin d) (Fin d) F →* Matrix (Block b c) (Block b c) F :=
  (Matrix.reindexAlgEquiv F F (monoEquivOfFin (Block b c) h).toEquiv).toMulEquiv.toMonoidHom

def blockEmb (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) :
    GL (Fin d) F →* blockTri (κ := F) b :=
  (Units.map ((blockMat b c).comp (toBlock b c h))).codRestrict (blockTri (κ := F) b) fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show blockMat b c _ i j = 0
    rw [blockMat_out b c _ i j (fun e => by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij; omega)]

theorem blockEmb_in (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) (g : GL (Fin d) F)
    (i j : Fin d) :
    ((blockEmb b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (monoEquivOfFin (Block b c) h i).1
      (monoEquivOfFin (Block b c) h j).1 = (g : Matrix (Fin d) (Fin d) F) i j := by
  show blockMat b c _ _ _ = _
  rw [blockMat_in]
  simp [toBlock]

theorem blockEmb_out (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) (g : GL (Fin d) F)
    (i j : Fin r) (hij : ¬ (b i = c ∧ b j = c)) :
    ((blockEmb b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j :=
  blockMat_out b c _ i j hij

variable {V : Type} [AddCommGroup V] [Module ℂ V] {V' : Type} [AddCommGroup V'] [Module ℂ V']

def blockRes (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ) {d : ℕ}
    (h : Fintype.card (Block b c) = d) : Representation ℂ (GL (Fin d) F) V :=
  σ.comp (blockEmb b c h)

def HasFactor (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ) {d : ℕ}
    (h : Fintype.card (Block b c) = d) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin d) F) W) : Prop :=
  ρ.IsIrreducible ∧
    IsIsotypicOfType (MonoidAlgebra ℂ (GL (Fin d) F)) (blockRes b σ c h).asModule ρ.asModule

def SameFactor (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ)
    (b' : Fin r → ℕ) (σ' : Representation ℂ (blockTri (κ := F) b') V') (c' : ℕ) : Prop :=
  ∃ (d : ℕ) (h : Fintype.card (Block b c) = d) (h' : Fintype.card (Block b' c') = d)
    (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (ρ : Representation ℂ (GL (Fin d) F) W),
    HasFactor b σ c h ρ ∧ HasFactor b' σ' c' h' ρ

def DistinctFactors (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) : Prop :=
  ∀ c ∈ Set.range b, ∀ c' ∈ Set.range b, c ≠ c' → ¬ SameFactor b σ c b σ c'

def SameFactorSet (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V)
    (b' : Fin r → ℕ) (σ' : Representation ℂ (blockTri (κ := F) b') V') : Prop :=
  (∀ c ∈ Set.range b, ∃ c' ∈ Set.range b', SameFactor b σ c b' σ' c') ∧
    ∀ c' ∈ Set.range b', ∃ c ∈ Set.range b, SameFactor b σ c b' σ' c'

def ProductIrreducible : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b : Fin r → ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ (blockTri (κ := F) b) V),
    IsCuspDatum b σ → DistinctFactors b σ → (parInd b σ).IsIrreducible

def ProductIsoIff : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'),
    IsCuspDatum b σ → DistinctFactors b σ → IsCuspDatum b' σ' → DistinctFactors b' σ' →
      (Nonempty ((parInd b σ).Equiv (parInd b' σ')) ↔ SameFactorSet b σ b' σ')

def CuspidalProduct : Prop := ProductIrreducible ∧ ProductIsoIff

end GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

open Formalism.L2.DIV GlobalTheory.FinGL Matrix

variable {F : Type} [Field F] {r d : ℕ}

def incl (F : Type) [Field F] (e : Fin d → Fin r) : Matrix (Fin r) (Fin d) F :=
  (1 : Matrix (Fin r) (Fin r) F).submatrix id e

theorem incl_transpose_mul (e : Fin d ↪ Fin r) : (incl F e)ᵀ * incl F e = 1 := by
  ext a a'
  simp [incl, Matrix.mul_apply, Matrix.one_apply, eq_comm]

def extendMat (e : Fin d ↪ Fin r) : Matrix (Fin d) (Fin d) F →* Matrix (Fin r) (Fin r) F where
  toFun g := 1 + incl F e * (g - 1) * (incl F e)ᵀ
  map_one' := by simp
  map_mul' g h := by
    have key : incl F e * (g - 1) * (incl F e)ᵀ * (incl F e * (h - 1) * (incl F e)ᵀ)
        = incl F e * ((g - 1) * (h - 1)) * (incl F e)ᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e)ᵀ, incl_transpose_mul, Matrix.one_mul]
    have e2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1) := by noncomm_ring
    rw [add_mul, mul_add, mul_add, key, e2]
    simp only [Matrix.mul_add, Matrix.add_mul, one_mul, mul_one, add_assoc]

theorem extendMat_apply (e : Fin d ↪ Fin r) (g : Matrix (Fin d) (Fin d) F) (i j : Fin r) :
    extendMat e g i j = (1 : Matrix (Fin r) (Fin r) F) i j +
      ∑ a', (∑ a, (if i = e a then 1 else 0) * (g - 1) a a') * (if j = e a' then 1 else 0) := by
  simp only [extendMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.add_apply, Matrix.mul_apply, incl,
    Matrix.transpose_apply, Matrix.submatrix_apply, id, Matrix.one_apply]

theorem extendMat_in (e : Fin d ↪ Fin r) (g : Matrix (Fin d) (Fin d) F) (a a' : Fin d) :
    extendMat e g (e a) (e a') = g a a' := by
  rw [extendMat_apply]
  simp [Matrix.one_apply]

theorem extendMat_out (e : Fin d ↪ Fin r) (g : Matrix (Fin d) (Fin d) F) (i j : Fin r)
    (h : i ∉ Set.range e ∨ j ∉ Set.range e) : extendMat e g i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  rw [extendMat_apply]
  rcases h with h | h
  · have : ∀ a, i ≠ e a := fun a ha => h ⟨a, ha.symm⟩
    simp [this]
  · have : ∀ a, j ≠ e a := fun a ha => h ⟨a, ha.symm⟩
    simp [this]

def block (b : Fin r → ℕ) (c : ℕ) : Finset (Fin r) := Finset.univ.filter fun i => b i = c

def blockEnum (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) : Fin d ↪ Fin r :=
  ((block b c).orderEmbOfFin h).toEmbedding

theorem blockEnum_mem (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (a : Fin d) :
    b (blockEnum b c h a) = c := by
  exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem (block b c) h a)).2

def blockHom (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    GL (Fin d) F →* blockTri (κ := F) b :=
  (Units.map (extendMat (blockEnum b c h))).codRestrict _ fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = 0
    rw [extendMat_out, Matrix.one_apply_ne]
    · rintro rfl
      exact lt_irrefl _ hij
    · by_contra hc
      push Not at hc
      obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hc
      rw [blockEnum_mem b c h, blockEnum_mem b c h] at hij
      exact lt_irrefl _ hij

def IsIsotypicOf {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G V) (ρ : Representation ℂ G W) : Prop :=
  (⨆ f : Representation.IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) = ⊤

def IsFactor {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ)
    (ρ : Representation ℂ (GL (Fin d) F) W) : Prop :=
  ρ.IsIrreducible ∧ ∃ h : (block b c).card = d,
    IsIsotypicOf (show Representation ℂ (GL (Fin d) F) V from σ.comp (blockHom F b c h)) ρ

def IsoGL {d d' : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (GL (Fin d) F) W) (ρ' : Representation ℂ (GL (Fin d') F) W') : Prop :=
  ∃ h : d' = d, Nonempty (Representation.Equiv ρ (h ▸ ρ' : Representation ℂ (GL (Fin d) F) W'))

theorem isoGL_iff {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (GL (Fin d) F) W) (ρ' : Representation ℂ (GL (Fin d) F) W') :
    IsoGL ρ ρ' ↔ Nonempty (Representation.Equiv ρ ρ') :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

def IsRegularCusp {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V)
    (d : ℕ → ℕ) (W : ℕ → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)) : Prop :=
  IsCuspDatum b σ ∧ (∀ c ∈ Set.range b, IsFactor b σ c (ρ c)) ∧
    ∀ c ∈ Set.range b, ∀ c' ∈ Set.range b, c ≠ c' → ¬ IsoGL (ρ c) (ρ c')

def ProductIrreducible : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b : Fin r → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (blockTri (κ := F) b) V)
    (d : ℕ → ℕ) (W : ℕ → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)),
    IsRegularCusp b σ d W ρ → (parInd b σ).IsIrreducible

def ProductIsoIff : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ)
    (b : Fin r → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (blockTri (κ := F) b) V)
    (d : ℕ → ℕ) (W : ℕ → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c))
    (b' : Fin r → ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (σ' : Representation ℂ (blockTri (κ := F) b') V')
    (d' : ℕ → ℕ) (W' : ℕ → Type) [∀ c, AddCommGroup (W' c)] [∀ c, Module ℂ (W' c)]
    (ρ' : ∀ c, Representation ℂ (GL (Fin (d' c)) F) (W' c)),
    IsRegularCusp b σ d W ρ → IsRegularCusp b' σ' d' W' ρ' →
    (Nonempty (Representation.Equiv (parInd b σ) (parInd b' σ')) ↔
      (∀ c ∈ Set.range b, ∃ c' ∈ Set.range b', IsoGL (ρ c) (ρ' c')) ∧
      (∀ c' ∈ Set.range b', ∃ c ∈ Set.range b, IsoGL (ρ c) (ρ' c')))

def IrrPar : Prop := ProductIrreducible ∧ ProductIsoIff

theorem isIsotypicOf_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) :
    IsIsotypicOf τ τ := by
  refine top_le_iff.1 (le_trans ?_ (le_iSup _ (Representation.IntertwiningMap.id τ)))
  intro v _
  exact ⟨v, rfl⟩

theorem trivial_irreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ ℂ) this
  · rcases eq_bot_or_eq_top (α := Submodule ℂ ℂ) S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

end GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

open Formalism.L2.DIV NumberField

variable {E : Type} [Field E] [NumberField E]


open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_kP (PP : _root_.Formalism.L2.DIV.Pl E) : Finite (_root_.Formalism.L2.DIV.kP PP) := by
  unfold _root_.Formalism.L2.DIV.kP
  exact Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot


open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_boundedLevelClassGroupFamily (Pg : Finset (_root_.Formalism.L2.DIV.Pl E)) (r : ℕ) :
    Finite (_root_.Formalism.L2.DIV.G0 Pg r) := by
  haveI : ∀ PP : ↥Pg, Finite (_root_.Formalism.L2.DIV.kP PP.1) := fun PP =>
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_kP PP.1
  unfold _root_.Formalism.L2.DIV.G0
  infer_instance

def IsCuspProdChar {κ : Type} [Field κ] {r : ℕ} (θ : GL (Fin r) κ → ℂ) : Prop :=
  ∃ (d : ℕ) (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := κ) b) (Fin d → ℂ)),
    FinGL.IsCuspDatum b σ ∧ ∀ x, θ x = (FinGL.parInd b σ).character x

def IsProdCuspChar {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) r (θ PP)) ∧
      ∀ x : G0 Pg r, s (χ x) = ∏ PP : ↥Pg, θ PP (x PP)

def levelMult {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  haveI : Fintype P.H := Fintype.ofFinite _
  (Nat.card P.H : K)⁻¹ * ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def nbar (Pg : Finset (Pl E)) (k : ℕ) : ℕ := ∏ PP ∈ Pg, Nat.card (kP PP) ^ k

def MultNear {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K) (N δ : ℝ) : Prop :=
  ∃ n : ℕ, levelMult P χ = (n : K) ∧ |(n : ℝ) - N| ≤ δ * N

def MultSharp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (f g r ρ k : ℕ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    Pg.card = 2 * f → 1 ≤ k → r = k + 2 * ρ + 1 → 0 < g → 4 * f * r ≤ g →
    (∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) → IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsProdCuspChar s Pg r χ →
      MultNear (PsharpSym Pg r ρ k ψ) χ (nbar Pg k) (8 * f * r / g) ∧
        MultNear (Psharp Pg r k ψ) χ (nbar Pg k) (8 * f * r / g)

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar_pos (Pg : Finset (_root_.Formalism.L2.DIV.Pl E)) (k : ℕ) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar Pg k := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar
  refine Finset.prod_pos fun PP _ => pow_pos ?_ k
  haveI := _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_kP PP
  haveI : Nonempty (_root_.Formalism.L2.DIV.kP PP) := ⟨0⟩
  exact Nat.card_pos

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericMultiplicityOne
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

variable {E : Type} [Field E] [NumberField E]

@[reducible] def resField (PP : Pl E) : Field (kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

attribute [local instance] resField

theorem finite_res (PP : Pl E) : Finite (kP PP) :=
  Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

attribute [local instance] finite_res

def IsIndCuspChar (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K] (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ (b : ↥Pg → Fin r → ℕ) (V : ↥Pg → Type) (_ : ∀ PP, AddCommGroup (V PP)) (_ : ∀ PP, Module ℂ (V PP))
    (_ : ∀ PP, FiniteDimensional ℂ (V PP))
    (σ : ∀ PP : ↥Pg, Representation ℂ (blockTri (κ := kP PP.1) (b PP)) (V PP)),
    (∀ PP : ↥Pg, IsCuspDatum (F := kP PP.1) (b PP) (σ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) =
      ∏ PP : ↥Pg, LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) (g PP))

theorem finite_parInd {F : Type} [Field F] [Finite F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := inferInstance

def GenericMultOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K), IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsIndCuspChar Pg r s χ →
      letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
      ∑ h : (P0 Pg r ψ).H, χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K) = (Nat.card (P0 Pg r ψ).H : K)

end GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne
end
end

