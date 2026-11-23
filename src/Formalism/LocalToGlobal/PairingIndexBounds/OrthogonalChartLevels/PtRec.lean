module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsGMapPrPSRatAS
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))


include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
def ptRec : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j →
    PtD D.host.F D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
  | 0, La => ptStep0 (I := I) (isUnit_det_gram0 D.sp) (k_pred D.R) (repP Lc p) a bad La.1 La.2
  | i + 1, La =>
      let X := Sx i La.1.1 La.1.2.1
      let S : StepG I (D.sp.X (i + 1)).rank :=
        { J := (D.sp.X (i + 1)).gram
          hJ := gram_herm D.sp.cm (D.sp.X (i + 1))
          hdet := gram_det_unit D.sp.cm (D.sp.X (i + 1))
          Lb := X.lev.Lb
          Uloc := X.lev.Uloc
          fr := X.fr
          U := X.lev.U
          U_eq := X.lev.U_eq }
      ptStep S (rank_step D i La.1.1) a bad La.1.2.2 La.2

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)



include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
def twC (v : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pl) (s : Fin ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.n' v)) : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.Qq v →+* ℂ_[p] :=
  letI := algKfC (cembCL D u h L h5 h2 he r Lc I ψ e).toCEmb
  tw (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) ℂ_[p] v s


variable {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)


variable (hst : FinStab (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))

end Formalism.L2.PairingIndexBounds.F
