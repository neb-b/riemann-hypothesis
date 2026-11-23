module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsHypA
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PtGComp

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsHyp
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def NotBad (I : LocId L p nV W Qq) : Prop :=
  ∀ v : Fin nV, (gp 0 : 𝓞 F) ∉ (I.plc v).asIdeal ∧ (gp 1 : 𝓞 F) ∉ (I.plc v).asIdeal ∧ (A.T : 𝓞 F) ∉ (I.plc v).asIdeal

abbrev splV (I : LocId L p nV W Qq) (v : Fin nV) :
    E ⊗[F] (I.plc v).adicCompletion F ≃+* (I.plc v).adicCompletion F × (I.plc v).adicCompletion F :=
  I.spl (I.plc v) (I.pl v).2

def IntSplit (I : LocId L p nV W Qq) : Prop :=
  ∀ (v : Fin nV) (t : E ⊗[F] (I.plc v).adicCompletion F), t ∈ intV E (I.plc v) ↔
    (splV I v t).1 ∈ ((I.plc v).adicCompletionIntegers F).toSubring ∧
      (splV I v t).2 ∈ ((I.plc v).adicCompletionIntegers F).toSubring

def SelfDualAtP (I : LocId L p nV W Qq) : Prop :=
  ∀ (v : Fin nV) (y : Fin R.k → E ⊗[F] (I.plc v).adicCompletion F), y ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb ↔
    ∀ z ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb,
      hform (sigR sp.cm.sig ((I.plc v).adicCompletion F))
        (sp.gram0.map (inclE (F := F) ((I.plc v).adicCompletion F))) z y ∈ intV E (I.plc v)

theorem fst_mulVec (I : LocId L p nV W Qq) (v : Fin nV) (x : GL (Fin R.k) (E ⊗[F] (I.plc v).adicCompletion F))
    (y : Fin R.k → E ⊗[F] (I.plc v).adicCompletion F) (a : Fin R.k) :
    (splV I v (((x : Matrix (Fin R.k) (Fin R.k) _) *ᵥ y) a)).1 =
      (((bc (fstV I v) x : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) *ᵥ fun b => (splV I v (y b)).1) a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul]
  rfl

theorem first_iff (I : LocId L p nV W Qq) (v : Fin nV) (x : GL (Fin R.k) (E ⊗[F] (I.plc v).adicCompletion F)) :
    (∀ y ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb, ∃ y' ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb,
      ∀ a, (splV I v (y' a)).1 = (splV I v (((x : Matrix (Fin R.k) (Fin R.k) _) *ᵥ y) a)).1) ↔
      ∀ a b, (((frV I v)⁻¹ * bc (fstV I v) x * frV I v : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F := by
  have hfr := I.fr_lat (I.plc v) (I.pl v).2
  refine Iff.trans ?_ (int_conj_iff ((I.plc v).adicCompletionIntegers F).toSubring (frV I v) (bc (fstV I v) x))
  constructor
  · intro h t ht
    obtain ⟨y, hy, e⟩ := (hfr t).2 ht
    obtain ⟨y', hy', e'⟩ := h y hy
    refine (hfr _).1 ⟨y', hy', fun a => ?_⟩
    rw [e' a, fst_mulVec]
    congr 2
    funext b
    exact e b
  · intro h y hy
    have h1 := h (fun b => (splV I v (y b)).1) ((hfr _).1 ⟨y, hy, fun _ => rfl⟩)
    obtain ⟨y', hy', e'⟩ := (hfr _).2 h1
    exact ⟨y', hy', fun a => by rw [e' a, fst_mulVec]⟩

theorem isHyperbolicAt_of_integralSplit (I : LocId L p nV W Qq) (hb : NotBad I) (h1 : IntSplit I) (h2 : SelfDualAtP I) : HypAtP I := by
  intro v x hx
  rw [L.Uloc_hyp (I.plc v) (hb v).1 (hb v).2.1 (hb v).2.2]
  have hlev : x ∈ levelVL sp.cm.sig sp.gram0 (I.plc v) L.Lb ↔ x ∈ stabGL (Formalism.L2.Herm.locL (I.plc v) L.Lb) :=
    ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨hx, h⟩⟩
  have einv : ((frV I v)⁻¹ * bc (fstV I v) x * frV I v)⁻¹ = (frV I v)⁻¹ * bc (fstV I v) x⁻¹ * frV I v := by
    rw [map_inv]; group
  rw [hlev, einv, ← first_iff, ← first_iff]
  constructor
  · intro h
    exact ⟨fun y hy => ⟨_, (h y).1 hy, fun _ => rfl⟩,
      fun y hy => ⟨_, (((stabGL (Formalism.L2.Herm.locL (I.plc v) L.Lb)).inv_mem h) y).1 hy, fun _ => rfl⟩⟩
  · rintro ⟨ha, hb'⟩
    exact stab_of_first (splV I v) (sigR sp.cm.sig ((I.plc v).adicCompletion F))
      (I.spl_sig (I.plc v) (I.pl v).2) ((I.plc v).adicCompletionIntegers F).toSubring
      (intV E (I.plc v)) (h1 v) (sp.gram0.map (inclE (F := F) ((I.plc v).adicCompletion F)))
      (Formalism.L2.Herm.locL (I.plc v) L.Lb) (h2 v) x hx ha hb'

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsOrb
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

abbrev HA (sp : Spaces R F E) : Subgroup (GA sp) :=
  (ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

abbrev KA (L : ColLevel R F E sp gp C A clsLat) : Subgroup (GA sp) :=
  L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

abbrev KA' (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Subgroup (GA sp) :=
  (Formalism.L2.Herm.awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

def ratA (sp : Spaces R F E) : UJ (sp.cm.sig : E →+* E) sp.gram0 →* GA sp :=
  ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).comp (UJ (sp.cm.sig : E →+* E) sp.gram0).subtype).codRestrict _
    (fun γ => Formalism.UG.P.rational_points_le_holds F E (Fin R.k) sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ⟨γ, γ.2, rfl⟩)

theorem ratA_mem (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) : ratA sp γ ∈ HA sp :=
  Subgroup.mem_subgroupOf.2 ⟨γ, γ.2, rfl⟩

theorem exists_ratA (x : GA sp) (hx : x ∈ HA sp) : ∃ γ, ratA sp γ = x := by
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 hx
  exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩

theorem mem_map_conj {G0 : Type} [Group G0] (S : Subgroup G0) (y g : G0) :
    g ∈ S.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * g * y ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : y⁻¹ * (MulAut.conj y).toMonoidHom u * y = u := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hu
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_gamC_iff (y : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _) ↔ y⁻¹ * ratA sp γ * y ∈ KA' L p :=
  mem_map_conj (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin R.k) E))

theorem prP_ratA (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) (v : Fin nV) :
    prP I hk (ratA sp γ) v = (castGL hk Qq).symm ((I.frQ v)⁻¹ * bc (I.iw v) (γ : GL (Fin R.k) E) * I.frQ v) := by
  rw [prP_apply, toF_symm]
  congr 1
  rw [map_mul, map_mul, map_inv]
  rfl

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfE
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {E LL : Type} [Field E] [Field LL] (e : LL →+* G.Kf)
  (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v) (t : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → E →+* LL)

def PosCompat : Prop :=
  ∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E), e (t v s x) = G.P.ι v ((G.P.σ v ^ s.val) (iw v x))

def ActE : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, (G.lev i).act v γ = Matrix.GeneralLinearGroup.map (iw v) a

def ChiRat : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

def RatTup : Prop :=
  ∀ L : G.P.Tup, G.P.IsLatTup L → ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, L v = colSpan (G.P.W v) ((a : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) E).map (iw v))

theorem ratLev_of (hp : PosCompat G e iw t) (ha : ActE G iw) (hc : ChiRat G e) : RatLev G e := by
  refine ⟨fun i γ v s => ?_, hc⟩
  obtain ⟨a, ha⟩ := ha i γ
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v]
  ext j k
  simp [gPosGL, hp v s]

theorem ratBasis_of (hp : PosCompat G e iw t) (hr : RatTup G iw) : RatBasis G e := by
  intro L hL v s
  obtain ⟨a, ha⟩ := hr L hL
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v, Formalism.MainNotions.G.LatticeSystems.la_extO_G]
  congr 1
  ext j k
  simp [Formalism.MainNotions.G.LatticeSystems.la_tw, hp v s]

end Formalism.L2.G.Cmp
end
end

