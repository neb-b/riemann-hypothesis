module

public import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def InPW (p : ℕ) [Fact p.Prime] (a : DV.KW p) : Prop :=
  ∃ b : WittVector p (AlgebraicClosure (ZMod p)), algebraMap _ (DV.KW p) b = a ∧ b.coeff 0 = 0

def ComplexEmbeddingsCompatible (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
    (jc p la).comp τ = D.what₂.embLL.comp e →
      ∀ x : 𝓞 D.host.E, (InPW p (τ (x : D.host.E)) ↔ la.1.valuation D.what₂.LL (e (x : D.host.E)) < 1)

def CuspTieX (X : DivX D) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) (x : (X.MjH j).V),
    X.geo.vanishOn (X.Yv j c) (X.Lw j c (DV.kapW D j)) (X.iMj j c x) (X.Ybd j c)

def IsoSp (S S' : letI := D.host.cmStar; HSpace D.host.E) : Prop :=
  letI := D.host.cmStar
  ∃ ι : S.V ≃ₗ[D.host.E] S'.V, HSpace.IsIsomEmb S S' ι.toLinearMap ∧
    S.L0.map (ι.toLinearMap.restrictScalars (𝓞 D.host.E)) = S'.L0

theorem IsoSp.rank_eq {S S' : letI := D.host.cmStar; HSpace D.host.E} (h : IsoSp S S') :
    (letI := D.host.cmStar; S.rank) = (letI := D.host.cmStar; S'.rank) := by
  obtain ⟨ι, -, -⟩ := h
  letI := D.host.cmStar
  rw [← S.rank_eq, ← S'.rank_eq]
  exact ι.finrank_eq

def IsoInv (F : ShimFam D G Lev) : Prop :=
  ∀ (w w' : Dat D Lev), IsoSp w.S w'.S → w.κ = w'.κ → w.j = w'.j → ∀ (h : w.Indef) (h' : w'.Indef),
    toShimX (F.U w) h (F.levPr w.κ) (F.levPr_prime w.κ) = toShimX (F.U w') h' (F.levPr w'.κ) (F.levPr_prime w'.κ)

def LevInTie (F : ShimFam D G Lev) (inK : Lev → ℕ → Prop) : Prop :=
  ∀ (w : Dat D Lev) (M : ℕ), (F.U w).pad.levIn M ↔ inK w.κ M

def GeoTiedP (X : DivX D) (inK : X.Lev → ℕ → Prop) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧ ComplexEmbeddingsCompatible F.jC ∧ CuspTieX X ∧
      IsoInv F ∧ LevInTie F inK

variable (D)

def famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO] [NumberField KO]
    (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL) (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) :
    ShimFam D (geoDegenerate D.what₂.LL D.what₂.Tau) PUnit where
  levPr := fun _ => Finset.univ.image D.host.g
  levPr_prime := fun _ p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  κg := PUnit.unit
  levPr_κg := rfl
  jC := jc
  ng := ng1
  U := fun w => shimUFl D jc w
  forms := formsFl D KO eO kL kL_eO _ _ _ (fun _ _ => true)

theorem isoInv_famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO]
    [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) : IsoInv (famFlJ D jc KO eO kL kL_eO) := by
  intro w w' hiso _ hj h h'
  exact (toShimX_fl D jc w h _).trans ((shimXFl_congr D jc _ _ _ _ hiso.rank_eq hj).trans
    (toShimX_fl D jc w' h' _).symm)

theorem levInTie_famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO]
    [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) :
    LevInTie (famFlJ D jc KO eO kL kL_eO) (fun _ _ => True) :=
  fun _ _ => Iff.rfl

end Formalism.L2.Geo
