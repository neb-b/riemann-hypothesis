module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

structure Places (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) where
  quad : Module.finrank F E = 2
  loc : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  L : ∀ p, LocE (loc p).Fp (loc p).Ep
  L_cj : ∀ p, (L p).cj = (loc p).cj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

namespace Places

variable (A : Places F E sig) {n : ℕ}

def bc (p : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) : Fin n → (A.loc p).Ep := fun i => (A.loc p).ιE (x i)

def lat (p : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (A.L p).O (Fin n → (A.loc p).Ep) :=
  Submodule.span (A.L p).O (A.bc p '' (Λ : Set (Fin n → E)))

def Ext (p : HeightOneSpectrum (𝓞 F)) (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) : Prop :=
  ∀ x, g' (A.bc p x) = A.bc p (g x)

def rat (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ p, ∃ g' ∈ K p, A.Ext p g g'}
  one_mem' := fun p => ⟨1, (K p).one_mem, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb p
    obtain ⟨a', ha1, ha2⟩ := ha p
    obtain ⟨b', hb1, hb2⟩ := hb p
    refine ⟨a' * b', (K p).mul_mem ha1 hb1, fun x => ?_⟩
    change a' (b' (A.bc p x)) = A.bc p (a (b x))
    rw [hb2 x, ha2 (b x)]
  inv_mem' := by
    intro a ha p
    obtain ⟨a', ha1, ha2⟩ := ha p
    refine ⟨a'⁻¹, (K p).inv_mem ha1, fun x => ?_⟩
    have h := ha2 (a.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    change a'.symm (A.bc p x) = A.bc p (a.symm x)
    rw [← h, LinearEquiv.symm_apply_apply]

end Places

structure GFrames (A : Places F E sig) (r k : ℕ) where
  Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E
  f : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  f' : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  es : Fin r → Fin (k + 2 * r + 1) → E
  es' : Fin r → Fin (k + 2 * r + 1) → E
  c : ∀ p, ((A.loc p).Fp)ˣ
  S : ∀ p, Frames (A.L p) r k
  Hm_eq : ∀ p, (S p).Hm = Hm.map (A.loc p).ιE
  f_eq : ∀ p (a : Fin (r + 1)), algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • (S p).f a = A.bc p (f a)
  f'_eq : ∀ p (a : Fin (r + 1)), algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • (S p).f' a = A.bc p (f' a)
  es_eq : ∀ p (a : Fin r), (S p).es a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)
  es'_eq : ∀ p (a : Fin r), (S p).es' a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es' a)
  c_unit : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite
  gg_fin : {p | (S p).gg = true}.Finite

namespace GFrames

variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)

abbrev V (_ : GFrames A r k) : Type := Fin (k + 2 * r + 1) → E

abbrev GLV : Type := G.V ≃ₗ[E] G.V

abbrev Lt : Type := Submodule (𝓞 E) G.V

abbrev Dat : Type := ∀ p, (G.S p).Datum

def N : Subgroup G.GLV := A.rat fun p => (G.S p).N

def N' : Subgroup G.GLV := A.rat fun p => (G.S p).N'

def St : Subgroup G.GLV := A.rat fun p => (G.S p).St

def K0 : Subgroup G.GLV := A.rat fun p => (G.S p).K0

def H0 : Subgroup G.GLV := A.rat fun p => (G.S p).H0

def stabD (d : G.Dat) : Subgroup G.GLV :=
  A.rat fun p => (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV (d p)

def IsTerm (d : G.Dat) (Λ : G.Lt) : Prop :=
  Submodule.IsLattice E Λ ∧ ∀ p, (G.S p).IsTerm (d p) (A.lat p Λ)

def DRel (d d' : G.Dat) : Prop :=
  ∃ g : G.GLV, ∀ p, ∃ g' ∈ (G.S p).H0, A.Ext p g g' ∧ g' • d p = d' p

def LRel (Λ Λ' : G.Lt) : Prop := ∃ g ∈ G.St, Λ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) = Λ'

def stabL (Λ : G.Lt) : Subgroup G.GLV :=
  A.rat fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)

def mu (Λ : G.Lt) : ℝ := invVol G.K0 (G.stabL Λ)

def om (d : G.Dat) (Λ : G.Lt) : ℂ := ∏ᶠ p, (G.S p).om (d p) (A.lat p Λ)

def amp (d : G.Dat) (P : G.Lt → Prop) : ℂ :=
  ∑' o : Quot G.LRel, if G.IsTerm d o.out ∧ P o.out then (G.mu o.out : ℂ) * G.om d o.out else 0

def mass (d : G.Dat) (P : G.Lt → Prop) : ℝ≥0∞ :=
  ∑' o : Quot G.LRel, if G.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (G.mu o.out) else 0

def Gen (d : G.Dat) (Λ : G.Lt) : Prop := ∀ p, (G.S p).BBzero (d p) (A.lat p Λ)

def Om : Set (HeightOneSpectrum (𝓞 F)) := {p | (G.S p).Hp ≠ 1}

def Ht : ℝ := ∏ᶠ p, (G.S p).Hp

def Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j)

def D (l : Fin (r + 2)) : E := lead G.Zh l

def TT : E := (∑ i, ∑ j, G.f (Fin.last r) i * G.Hm i j * sig (G.f (Fin.last r) j)) *
  ∑ i, ∑ j, G.f' (Fin.last r) i * G.Hm i j * sig (G.f' (Fin.last r) j)

def Gr : E := G.D (Fin.last (r + 1)) * sig (G.D (Fin.last (r + 1))) -
  G.TT * (G.D (Fin.last r).castSucc * sig (G.D (Fin.last r).castSucc))

end GFrames

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

structure Coord (P : LocNG.FPair H r) (S : Frames M.L r k) where
  e : V ≃ₗ[E] S.V
  h_eq : ∀ x y, S.h (e x) (e y) = H.h x y
  f_eq : ∀ a, S.f a = e (P.A.f a)
  f'_eq : ∀ a, S.f' a = e (P.B.f a)
  es_eq : ∀ a, S.es a = e (P.A.es a)
  es'_eq : ∀ a, S.es' a = e (P.B.es a)
  T_eq : (S.T : F) = P.A.T
  T'_eq : (S.T' : F) = P.B.T
  gg_none : M.split = none → S.gg = false
  gg_some : ∀ g, M.split = some g → S.gg = true ∧ S.ϖ = g.q

namespace Coord

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

def grp : (V ≃ₗ[E] V) ≃* S.GLV where
  toFun g := (c.e.symm.trans g).trans c.e
  invFun g := (c.e.trans g).trans c.e.symm
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' a b := by ext v; simp

def lat (Λ : Submodule M.L.O V) : Submodule M.L.O S.V :=
  Λ.map ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O)

def inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) : Submodule M.L.O S.V :=
  c.lat ((L.comap ((H.mkW f).restrictScalars M.L.O)).map ((H.perp (H.X f)).subtype.restrictScalars M.L.O))

def dat (d : LocNG.Datum P) : S.Datum :=
  (c.inn P.A.f d.L, c.inn P.B.f d.L',
    {p | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧
      ((M.split = none ∧ H.mkW P.B.f x' ∈ d.L' ∧ H.mkW P.A.f x ∈ d.L) ∨
        (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io)})

end Coord

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContModel

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.ContModel.relVol_of_le {W : Type} [AddCommGroup W]
    {W0 A B : AddSubgroup W} (h : B ≤ A) (hB : B.relIndex W0 ≠ 0) :
    _root_.GlobalTheory.HL.relVol W0 A = B.relIndex A * _root_.GlobalTheory.HL.relVol W0 B := by
  unfold _root_.GlobalTheory.HL.relVol
  have h1 := AddSubgroup.relIndex_inf_mul_relIndex W0 B A
  have h2 := AddSubgroup.relIndex_inf_mul_relIndex B W0 A
  have h3 := AddSubgroup.relIndex_inf_mul_relIndex B A W0
  rw [inf_eq_left.mpr h] at h1 h3
  rw [inf_comm W0 B] at h1
  rw [inf_comm W0 A] at h2
  rw [← h3] at hB ⊢
  have hd : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hB
  have hα : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hB
  have key : (W0.relIndex B : ℝ) * B.relIndex A = B.relIndex (A ⊓ W0) * W0.relIndex A := by
    exact_mod_cast h1.trans h2.symm
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * key

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private theorem ncard_image_mk_eq_mul_relIndex_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A)
    {S : Set W} (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  set Ab : AddSubgroup (W ⧸ B) := A.map (QuotientAddGroup.mk' B) with hAb
  set T : Set ((W ⧸ B) ⧸ Ab) :=
    (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S) with hT
  have hpre : (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T =
      (QuotientAddGroup.mk : W → W ⧸ B) '' S := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
      induction y using QuotientAddGroup.induction_on with
      | H w =>
        rw [QuotientAddGroup.eq, hAb, AddSubgroup.mem_map] at hz
        obtain ⟨a, ha, hax⟩ := hz
        have hax' : ((a : W) : W ⧸ B) = -((x : W) : W ⧸ B) + (w : W ⧸ B) := hax
        refine ⟨x + a, hS x hx a ha, ?_⟩
        rw [QuotientAddGroup.mk_add, hax']
        abel
    · intro hy
      exact ⟨y, hy, rfl⟩
  have e1 : Nat.card ((QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T) = Nat.card Ab * Nat.card T :=
    (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet Ab T)).trans (Nat.card_prod _ _)
  have e2 : Nat.card Ab = B.relIndex A := by
    rw [hAb, ← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
      QuotientAddGroup.ker_mk']
  have e3 : ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard = T.ncard := by
    rw [← Set.ncard_image_of_injective T (QuotientAddGroup.quotientQuotientEquivQuotient B A h).injective]
    congr 1
    rw [hT, Set.image_image, Set.image_image]
    rfl
  rw [← hpre, ← Nat.card_coe_set_eq, e1, e2, e3, Nat.card_coe_set_eq, mul_comm]


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.ContModel.cont_eq {W : Type} [AddCommGroup W]
    {W0 A : AddSubgroup W} {S : Set W} (hA : _root_.GlobalTheory.HL.GoodSub W0 A S) :
    _root_.GlobalTheory.HL.cont W0 S =
      (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * _root_.GlobalTheory.HL.relVol W0 A := by
  have hS : _root_.GlobalTheory.HL.IsCO W0 S := ⟨A, hA⟩
  rw [_root_.GlobalTheory.HL.cont, dite_eq_left hS]
  have hA' : _root_.GlobalTheory.HL.GoodSub W0 hS.choose S := hS.choose_spec
  have hB : (A ⊓ hS.choose).relIndex W0 ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hA.1 hA'.1
  rw [_root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hB,
    _root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hB,
    ← mul_assoc, ← mul_assoc]
  congr 1
  exact_mod_cast (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hA'.2.2.1).symm.trans
    (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hA.2.2.1)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.gramT_rmul (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    _root_.GlobalTheory.HL.gramT L Hm (_root_.GlobalTheory.HL.rmul x A) =
      _root_.GlobalTheory.HL.cT L A * _root_.GlobalTheory.HL.gramT L Hm x * A := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.GlobalTheory.HL.gramT, _root_.GlobalTheory.HL.rmul, _root_.GlobalTheory.HL.hf,
    _root_.GlobalTheory.HL.cT, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.cj_mem (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def] at *
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.gramT_thick (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : 𝒪[F]) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (Ω : Set (Fin m → Fin n → E)) (Γ : Matrix (Fin m) (Fin m) E)
    (i : ℕ) (hΩ : ∀ y ∈ Ω, _root_.GlobalTheory.HL.gramT L Hm y = Γ) :
    ∀ x ∈ _root_.GlobalTheory.HL.thick L ϖ Ω i,
      _root_.GlobalTheory.HL.gramT L Hm x ∈ _root_.GlobalTheory.HL.horb L ϖ Γ i := by
  rintro x ⟨y, hy, A, hA, rfl⟩
  exact ⟨A, hA, by rw [_root_.GlobalTheory.HL.ContModel.gramT_rmul, hΩ y hy]⟩

end GlobalTheory.HL.ContModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.IdxInt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def Ysp (J : ℕ) : Submodule E S.V := S.spanTo S.f J ⊔ S.spanTo S.f' J

def refB (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup (S.V × S.V) :=
  ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
    (Λ.toAddSubgroup.map (algebraMap F E S.th • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom).comap
      (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

def refU (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.V :=
  Λ.toAddSubgroup ⊓ (perp L S.Hm (S.Ysp J)).toAddSubgroup

def refT : AddSubgroup E :=
  (AddMonoidHom.id E + (L.cj : E →+* E).toAddMonoidHom).ker ⊓
    L.O.toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap F E ((S.ϖ : F) ^ S.a)))

abbrev MW : Type := (S.V × S.V) × S.V × E

def refA (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.MW :=
  (S.refB J Λ).prod ((S.refU J Λ).prod S.refT)

def sOf (w : S.MW) : E := algebraMap F E 2⁻¹ * S.h w.2.1 w.2.1 + w.2.2

def Mv (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.IsMove J d Λ w.1.1 w.1.2 w.2.1 (S.sOf w)

def MvTo (J : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.Mv J d Λ w ∧ (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w)

def NoLeak (Λ : Submodule L.O S.V) (u : S.V) : Prop := ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1

def InZ (u : S.V) : Prop := ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)

def chiM (j : Fin r) (d : S.Datum) (Λ : Submodule L.O S.V) (b : S.V × S.V) (u : S.V) : ℂ :=
  L.psi0 (-(algebraMap F E S.th⁻¹ *
    S.h (S.h b.1 (S.es j) • S.fr d Λ j.succ + S.h b.2 (S.es' j) • S.fr' d Λ j.succ) u))

def cK (β βJ : ℕ) : ℝ := (S.q : ℝ) ^ S.a * β / βJ

def kern (β J βJ : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) : ℝ :=
  S.cK β βJ * (cint (S.refA J Λ) (ind (S.MvTo J d Λ Λ₁))).re

end GlobalTheory.HL.Frames
end
end

