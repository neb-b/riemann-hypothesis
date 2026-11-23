module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.LamHLocPrinc
section
noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Loc

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}

def HLoc (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) H

def lamHLoc {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HLoc F v H →* Z :=
  congChar _ (algMapV_injective F v) _ _ lam

end Loc

section Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))

def HU (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)) :=
  UPts σE J (v.adicCompletion F) ⊓ (HLoc F v H).comap (toFr v spl fr)

def lamHU {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HU σE J v spl fr H →* Z :=
  (lamHLoc F v H lam).comp (((toFr v spl fr).subgroupComap (HLoc F v H)).comp (Subgroup.inclusion inf_le_right))

end Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

structure LevAtGH (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (gp : Fin 2 → ℕ)
    (splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))) where

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin N) (v.adicCompletion F)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin N → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      ∀ b, (splitG i v h (y b)).1 = x b) ↔
      ∀ b, (((frG i v h)⁻¹ : GL (Fin N) (v.adicCompletion F)) : Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Uloc v = HU σE J v (splitG i v h) (frG i v h) (H i v h)

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))}
    {H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))}
    {Z : Type} [CommGroup Z]

def LevAtGH.lamV (X : LevAtGH σE J gp splitG Lb Uloc H) (lam : ∀ i v h, H i v h →* Z) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) : Uloc v →* Z :=
  (lamHU σE J v (splitG i v h) (X.frG i v h) (H i v h) (lam i v h)).comp (Subgroup.inclusion (le_of_eq (X.Uloc_g i v h)))

def LevAtGH.lamGlob (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ i : Fin 2, prodChar (placesOver F (gp i)) Uloc
    (fun v hv => X.lamV lam i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
    Up (fun v hv => hUp i v ((mem_placesOver F (gp i) (hg i) v).1 hv))

def LevAtGH.lamG (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z :=
  X.lamGlob hg lam (awayG σE J Uloc p) (fun i v h => awayG_le_comap p v (not_mem_of_coprime (hp i) v h))

def LevAtGH.typeX (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.lamG hg lam p hp)⁻¹

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat}

structure GChartTie {p : ℕ} {G : GAtP p} (X : Formalism.L2.Herm.GLevTie L G) {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {cmp : Type}
    (em : cmp → Lv.compS i) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (ψ : awayG sp.cm.sig J Uloc p →* G.Oˣ) (eps : UJ (sp.cm.sig : E →+* E) J →* G.Oˣ) where

  em_inj : Function.Injective em

  rk : (Fl.Pj (i + 1)).m + 1 = N

  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (X.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

  yG : cmp → UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)
  yG_p : ∀ c (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    bc (prV (E := E) w) (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1
  yG_bij : Function.Bijective (fun c : cmp => (Quotient.mk'' (yG c) : compG sp.cm.sig J Uloc p))

  gamI : ∀ c, (Lv.levS i (em c)).Γ →* UJ (sp.cm.sig : E →+* E) J
  gamI_inj : ∀ c, Function.Injective (gamI c)
  gamI_range : ∀ c (γ : UJ (sp.cm.sig : E →+* E) J), γ ∈ (gamI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin N) E) ∈
      (awayG sp.cm.sig J Uloc p).map (MulAut.conj (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom

  act_eq : ∀ c (v : Fin G.P.nV) w (h : (X.pl v).1 = w) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (γ : (Lv.levS i (em c)).Γ)
    (a b : Fin ((Fl.Pj (i + 1)).m + 1)) (a' b' : Fin N), (a : ℕ) = a' → (b : ℕ) = b' →
    X.eQ v w h (((Lv.levS i (em c)).act v γ : GL (Fin ((Fl.Pj (i + 1)).m + 1)) (G.P.Qq v)) a b) =
      (((fr w hw)⁻¹ * bc ((RingHom.fst _ _).comp (X.spl w hw).toRingHom)
        (bc (inclE (F := F) (w.adicCompletion F)) (gamI c γ : GL (Fin N) E)) * fr w hw :
          GL (Fin N) (w.adicCompletion F)) : Matrix (Fin N) (Fin N) (w.adicCompletion F)) a' b'

  chi_eq : ∀ c (γ : (Lv.levS i (em c)).Γ) (x : awayG sp.cm.sig J Uloc p),
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹ *
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamI c γ : GL (Fin N) E) * yG c →
    (Lv.levS i (em c)).χ γ = ψ x * eps (gamI c γ)

variable {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  {n' : ℕ} {O Kf : Type} [IsDomain W] [IsDiscreteValuationRing W]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}


def ChartsCover {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {Cb : Type} {cmp : Cb → Type}
    (em : ∀ β, cmp β → Lv.compS i) : Prop :=
  Function.Bijective (fun x : Σ β, cmp β => em x.1 x.2)

end Formalism.L2.G
end
end

