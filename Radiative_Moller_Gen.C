//================================================================================
//================================================================================
//      Radiative Moller Generator
//      Charles Epstein, MIT, Fall 2013
//      Soft Radiative Corrections based on Denner & Pozzorini, 1999
//      Hard Brehmsstralung based on Petriello, 2003 (E158)
//
//      Cross section integrates approximately to values from Petriello's paper
//
//      Known bugs:
//
//      Some values of the brehmsstralung cross-section are negative,
//      which cannot be.  For example, the conditions:
//      Ek: 0.176759 tk: 3.03449 tqr: 3.13673 pqr: 6.21796, produce cs: -4042.85
//      Obviously this is wrong.  These sets of coordinates that produce negative
//      cross-sections are isolated spots however, and could be a result of evaluating
//      the bremsstralung matrix element segments at the edge of the regions of
//      their validity.
//================================================================================
//================================================================================


#include "Riostream.h"
#include "TFile.h"
#include "TFoam.h"
#include "TLorentzVector.h"
#include "TF1.h"
#include "TF2.h"
#include "TH1.h"
#include "TH2D.h"
#include "TMath.h"
#include "TCanvas.h"
#include "TRandom3.h"
#include "TSystem.h"
#include "TStyle.h"
#include <complex>

//Constants
const double Tbeam = 48000.; //Set this!


const double me = 0.511;
const double Ebeam = Tbeam+me;
const double sw2 = 0.2216189;
const double cw2 = 1.-sw2;

const double pi = 4.0*atan(1.0);
const double twopi = 2.*pi;

const double Pbeam = sqrt(pow(Ebeam,2.)-pow(me,2.));
const double betacm = Pbeam/(Ebeam+me);
const double gammacm = 1./sqrt(1.-pow(betacm,2.));

const double Ecm = gammacm*Ebeam - gammacm*betacm*Pbeam + gammacm*me;
const double Pcm = sqrt(pow(Ecm/2.,2)-pow(me,2.));//momentum of either beam in CM frame
const double Ecmp = Ecm/2.; //Ecm per particle


const double Pcmp = sqrt(pow(Ecmp,2)-pow(me,2.));//momentum of either beam in CM frame
const double r0 = (1./137.)*(1.97e-11)/me;


const double alpha = 1./137.;
const double ec= sqrt(4.*pi*(1./137.)); //electron charge
const double mz = 91188.; // Z boson mass
const double mz2 = pow(mz,2.);
const double mw2 = mz2*cw2;

const double gv = -0.25+sw2; //vector coupling
const double ga = 0.25; //axial coupling
const double se = 4.*Ecmp*Ecmp; //Elastic Mandelstam S ("s" was unavailable)
const double Lumi = 1.e30; //cm^2 s^-1 - gives CS in microbarns





///////////////////////////////////////////////////////////////////
//SOFT BREHM / ELASTIC KINEMATICS
//Denner & Pozzorini, 1999
//Electromagnetic Section of their paper, includes Z bosons though
///////////////////////////////////////////////////////////////////

//Mandelstam T ("t" was unavailable)
//Double_t te(Double_t x) {return (2.0*me*me-2.0*(E*Ep(x)-p*pf(x)*cos(x)));}
double te(double x)
    {
    return -4.*Ecmp*Ecmp*pow(sin(x/2.),2.);
    }

//Mandelstam U
//Double_t ue(Double_t x) {return 4.0*pow(me,2) - sv - tv(x);}
double ue(double x)
    {
    return -4.*Ecmp*Ecmp*pow(cos(x/2.),2.);
    }


std::complex<double> se_c (se,0); //Need this for some calculations


//Squared Tree-Level Matrix element - does not take m->0 limit
Double_t M2(Double_t x)
    {
    return 64.0*pow(pi,2.)*pow(alpha,2.)*(pow(me,4.)/pow(te(x),2)*
                                          ((pow(se,2)+pow(ue(x),2))/(2.*pow(me,4))+4.*te(x)/pow(me,2)-4.0)+pow(me,4)/
                                          pow(ue(x),2)*((pow(se,2)+pow(te(x),2))/(2.0*pow(me,4))+4.0*ue(x)/pow(me,2)-4.)+
                                          pow(me,4)/(ue(x)*te(x))*(se/pow(me,2)-2.0)*(se/pow(me,2)-6.0));
    }


///////////////////////////////////////////////////////////////////
//Below, the 'I' are relations for box diagrams
///////////////////////////////////////////////////////////////////

double epsilon = 0.;
std::complex<double> ieps (0,epsilon);

std::complex<double> I5ggST(double x)
    {
    return alpha/twopi*( se/(2.*(se+te(x))) * log(te(x)/(se+ieps)) -
                         se*(se+2.*te(x))/(4.*pow(se+te(x),2.)) * (pow(log(te(x)/(se+ieps)),2.)+pi*pi));
    }

std::complex<double> I5ggSU(double x)
    {
    return alpha/twopi*(se/(2.*(se+ue(x)))*log(ue(x)/(se+ieps)) -
                        se*(se+2.*ue(x))/(4.*pow(se+ue(x),2.))*(pow(log(ue(x)/(se+ieps)),2.)+pi*pi));
    }

std::complex<double> I5ggTU(double x)
    {
    return alpha/twopi*(te(x)/(2.*(te(x)+ue(x)))*log(ue(x)/(te(x)+ieps)) -
                        te(x)*(te(x)+2.*ue(x))/(4.*pow(te(x)+ue(x),2.))*(pow(log(ue(x)/(te(x)+ieps)),2.)+pi*pi));
    }

std::complex<double> I5ggTS(double x)
    {
    return alpha/twopi*(te(x)/(2.*(te(x)+se))*log(se/(te(x)+ieps)) -
                        te(x)*(te(x)+2.*se)/(4.*pow(te(x)+se,2.))*(pow(log(se/(te(x)+ieps)),2.)+pi*pi));
    }

std::complex<double> I5ggUT(double x)
    {
    return alpha/twopi*(ue(x)/(2.*(ue(x)+te(x)))*log(te(x)/(ue(x)+ieps)) -
                        ue(x)*(ue(x)+2.*te(x))/(4.*pow(ue(x)+te(x),2.))*(pow(log(te(x)/(ue(x)+ieps)),2.)+pi*pi));
    }

std::complex<double> I5ggUS(double x)
    {
    return alpha/twopi*(ue(x)/(2.*(ue(x)+se))*log(se/(ue(x)+ieps)) -
                        ue(x)*(ue(x)+2.*se)/(4.*pow(ue(x)+se,2.))*(pow(log(se/(ue(x)+ieps)),2.)+pi*pi));
    }



std::complex<double> I5gzTS(double x)
    {
    return alpha/twopi*(te(x)-mz2)/(2.*(te(x)+se))*(
               std::log(se_c/(te(x)-mz2)) - mz2/te(x) * std::log(mz2/(mz2-te(x)))
               +(te(x)+2.*se+mz2)/(te(x)+se) * (TMath::DiLog(te(x)/mz2)-
                       TMath::DiLog(-se/mz2)+std::log(-se_c/mz2)*std::log((mz2-te(x))/(mz2+se))));
    }


std::complex<double> I5gzTU(double x)
    {
    return alpha/twopi*(te(x)-mz2)/(2.*(te(x)+ue(x)))*(
               std::log(ue(x)/(te(x)-mz2))-mz2/te(x)*std::log(mz2/(mz2-te(x)))
               +(te(x)+2.*ue(x)+mz2)/(te(x)+ue(x))*(TMath::DiLog(te(x)/mz2)-
                       TMath::DiLog(-ue(x)/mz2)+std::log(-ue(x)/mz2)*std::log((mz2-te(x))/(mz2+ue(x)))));
    }


std::complex<double> I5gzUS(double x)
    {
    return alpha/twopi*(ue(x)-mz2)/(2.*(ue(x)+se))*(
               std::log(se_c/(ue(x)-mz2))-mz2/ue(x)*std::log(mz2/(mz2-ue(x)))
               +(ue(x)+2.*se+mz2)/(ue(x)+se)*(TMath::DiLog(ue(x)/mz2)-
                       TMath::DiLog(-se/mz2)+std::log(-se_c/mz2)*std::log((mz2-ue(x))/(mz2+se))));
    }


std::complex<double> I5gzUT(double x)
    {
    return alpha/twopi*(ue(x)-mz2)/(2.*(ue(x)+te(x)))*(
               std::log(te(x)/(ue(x)-mz2))-mz2/ue(x)*std::log(mz2/(mz2-ue(x)))
               +(ue(x)+2.*te(x)+mz2)/(ue(x)+te(x))*(TMath::DiLog(ue(x)/mz2)-
                       TMath::DiLog(-te(x)/mz2)+std::log(-te(x)/mz2)*std::log((mz2-ue(x))/(mz2+te(x)))));
    }
std::complex<double> I5gzST(double x)
    {
    return alpha/twopi*(se-mz2)/(2.*(se+te(x)))*(
               std::log(te(x)/(se_c-mz2))-mz2/se*std::log(mz2/(mz2-se))
               +(se+2.*te(x)+mz2)/(se+te(x))*(TMath::DiLog(se/mz2)-
                       TMath::DiLog(-te(x)/mz2)+std::log(-te(x)/mz2)*std::log((mz2-se)/(mz2+te(x)))));
    }



std::complex<double> I5gzSU(double x)
    {
    return alpha/twopi*(se-mz2)/(2.*(se+ue(x)))*(
               std::log(ue(x)/(se_c-mz2))-mz2/se*std::log(mz2/(mz2-se_c))
               +(se+2.*ue(x)+mz2)/(se+ue(x))*(TMath::DiLog(se/mz2)-
                       TMath::DiLog(-ue(x)/mz2)+std::log(-ue(x)/mz2)*std::log((mz2-se)/(mz2+ue(x)))));
    }

///////////////////////////////////////////////////////////////////
//More Definitions for D&P paper
///////////////////////////////////////////////////////////////////

double Z = 3.*log(se/(me*me))+2.*pi*pi/3.-4.;

double Xp (double x)
    {
    return pow(log(ue(x)/te(x)),2.)+pi*pi/3.;
    }

double Yt (double x)
    {
    return -pow(log(-te(x)/se),2.)-2.*log(-te(x)/se)*log((te(x)+se)/se)+3.*log(-te(x)/se)-pi*pi;
    }

double Yu (double x)
    {
    return -pow(log(-ue(x)/se),2.)-2.*log(-ue(x)/se)*log((ue(x)+se)/se)+3.*log(-ue(x)/se)-pi*pi;
    }


double gam (double x, double dE)
    {
    return 4.*alpha/pi*log(2.*dE/sqrt(se))*(log(ue(x)*te(x)/(se*me*me))-1.);
    }

double dut (double x)
    {
    return -log(-te(x)/se)*(log((mz2-ue(x))/(-ue(x)))+
                            log((mz2-ue(x))/mz2))+TMath::DiLog((mz2+te(x))/mz2)-TMath::DiLog((mz2+se)/se);
    }
double dtu (double x)
    {
    return -log(-ue(x)/se)*(log((mz2-te(x))/(-te(x)))+
                            log((mz2-te(x))/mz2))+TMath::DiLog((mz2+ue(x))/mz2)-TMath::DiLog((mz2+se)/se);
    }


double gzm = (2.*sw2-1.)/(2.*sqrt(sw2*cw2));
double gzp = sqrt(sw2/cw2);


///////////////////////////////////////////////////////////////////
//Matrix Elements, D&P
///////////////////////////////////////////////////////////////////

double M1u (double x)
    {
    return 2.*se/ue(x);
    }

double M2u (double x)
    {
    return 2.*te(x)/ue(x);
    }

double M1t (double x)
    {
    return 2.*se/te(x);
    }

double M3t (double x)
    {
    return 2.*ue(x)/te(x);
    }


double M1uzp (double x)
    {
    return gzp*gzp*2.*se/(ue(x)-mz2);
    }

double M1uzm (double x)
    {
    return gzm*gzm*2.*se/(ue(x)-mz2);
    }

double M2uz (double x)
    {
    return gzp*gzm*2.*te(x)/(ue(x)-mz2);
    }

double M1tzp (double x)
    {
    return gzp*gzp*2.*se/(te(x)-mz2);
    }

double M1tzm (double x)
    {
    return gzm*gzm*2.*se/(te(x)-mz2);
    }

double M3tz (double x)
    {
    return gzp*gzm*2.*ue(x)/(te(x)-mz2);
    }



///////////////////////////////////////////////////////////////////
//Correction Factors, D&P
///////////////////////////////////////////////////////////////////

std::complex<double> delu1g (double x)
    {
    return alpha/twopi*(Z+Yu(x)+Xp(x))+2.*I5ggUT(x);
    }
std::complex<double> delu2g (double x)
    {
    return alpha/twopi*(Z+Yu(x)+Xp(x))-2.*I5ggUS(x);
    }

std::complex<double> delt1g (double x)
    {
    return alpha/twopi*(Z+Yt(x)+Xp(x))+2.*I5ggTU(x);
    }

std::complex<double> delt3g (double x)
    {
    return alpha/twopi*(Z+Yt(x)+Xp(x))-2.*I5ggTS(x);
    }

std::complex<double> delu1z (double x)
    {
    return alpha/twopi*(Z+Yu(x)+Xp(x)+2.*dut(x))+4.*I5gzUT(x);
    }

std::complex<double> delu2z (double x)
    {
    return alpha/twopi*(Z+Yu(x)+Xp(x)+2.*dut(x))-4.*I5gzUS(x);

    }

std::complex<double> delt1z (double x)
    {
    return alpha/twopi*(Z+Yt(x)+Xp(x)+2.*dtu(x))+4.*I5gzTU(x);

    }

std::complex<double> delt3z (double x)
    {
    return alpha/twopi*(Z+Yt(x)+Xp(x)+2.*dtu(x))-4.*I5gzTS(x);

    }

///////////////////////////////////////////////////////////////////
//Soft Correction = Delta (CS), D&P
///////////////////////////////////////////////////////////////////

double corr_soft(double x, double dE)
    {
    return 0.25*alpha*alpha/(4.*se)*(

               //M1, lambda +, Z
               std::real(M1u(x)*M1u(x) * (delu1g(x) + std::conj(delu1g(x)) + gam(x,dE)) )+
               std::real(M1u(x)*M1uzp(x) * (delu1g(x) + std::conj(delu1z(x)) + gam(x,dE)) )+
               std::real(M1u(x)*M1tzp(x) * (delu1g(x) + std::conj(delt1z(x)) + gam(x,dE)) )+
               std::real(M1u(x)*M1t(x) * (delu1g(x) + std::conj(delt1g(x)) + gam(x,dE)) )+

               std::real(M1t(x)*M1uzp(x) * (delt1g(x)+std::conj(delu1z(x))+gam(x,dE)))+
               std::real(M1t(x)*M1u(x) * (delt1g(x)+std::conj(delu1g(x))+gam(x,dE)))+
               std::real(M1t(x)*M1t(x) * (delt1g(x)+std::conj(delt1g(x))+gam(x,dE)))+
               std::real(M1t(x)*M1tzp(x) * (delt1g(x)+std::conj(delt1z(x))+gam(x,dE)))+

               std::real(M1uzp(x)*M1u(x) * (delu1z(x) + std::conj(delu1g(x)) + gam(x,dE)) )+
               std::real(M1uzp(x)*M1uzp(x) * (delu1z(x) + std::conj(delu1z(x)) + gam(x,dE)) )+
               std::real(M1uzp(x)*M1tzp(x) * (delu1z(x) + std::conj(delt1z(x)) + gam(x,dE)) )+
               std::real(M1uzp(x)*M1t(x) * (delu1z(x) + std::conj(delt1g(x)) + gam(x,dE)) )+

               std::real(M1tzp(x)*M1u(x) * (delt1z(x) + std::conj(delu1g(x)) + gam(x,dE)) )+
               std::real(M1tzp(x)*M1uzp(x) * (delt1z(x) + std::conj(delu1z(x)) + gam(x,dE)) )+
               std::real(M1tzp(x)*M1tzp(x) * (delt1z(x) + std::conj(delt1z(x)) + gam(x,dE)) )+
               std::real(M1tzp(x)*M1t(x) * (delt1z(x) + std::conj(delt1g(x)) + gam(x,dE)) )+

               //M1, lambda -, Z
               std::real(M1u(x)*M1u(x) * (delu1g(x) + std::conj(delu1g(x)) + gam(x,dE)) )+
               std::real(M1u(x)*M1uzm(x) * (delu1g(x) + std::conj(delu1z(x)) + gam(x,dE)) )+
               std::real(M1u(x)*M1tzm(x) * (delu1g(x) + std::conj(delt1z(x)) + gam(x,dE)) )+
               std::real(M1u(x)*M1t(x) * (delu1g(x) + std::conj(delt1g(x)) + gam(x,dE)) )+

               std::real(M1t(x)*M1uzm(x) * (delt1g(x)+std::conj(delu1z(x))+gam(x,dE)))+
               std::real(M1t(x)*M1u(x) * (delt1g(x)+std::conj(delu1g(x))+gam(x,dE)))+
               std::real(M1t(x)*M1t(x) * (delt1g(x)+std::conj(delt1g(x))+gam(x,dE)))+
               std::real(M1t(x)*M1tzm(x) * (delt1g(x)+std::conj(delt1z(x))+gam(x,dE)))+

               std::real(M1uzm(x)*M1u(x) * (delu1z(x) + std::conj(delu1g(x)) + gam(x,dE)) )+
               std::real(M1uzm(x)*M1uzm(x) * (delu1z(x) + std::conj(delu1z(x)) + gam(x,dE)) )+
               std::real(M1uzm(x)*M1tzm(x) * (delu1z(x) + std::conj(delt1z(x)) + gam(x,dE)) )+
               std::real(M1uzm(x)*M1t(x) * (delu1z(x) + std::conj(delt1g(x)) + gam(x,dE)) )+

               std::real(M1tzm(x)*M1u(x) * (delt1z(x) + std::conj(delu1g(x)) + gam(x,dE)) )+
               std::real(M1tzm(x)*M1uzm(x) * (delt1z(x) + std::conj(delu1z(x)) + gam(x,dE)) )+
               std::real(M1tzm(x)*M1tzm(x) * (delt1z(x) + std::conj(delt1z(x)) + gam(x,dE)) )+
               std::real(M1tzm(x)*M1t(x) * (delt1z(x) + std::conj(delt1g(x)) + gam(x,dE)) )+

               //M2, Z
               std::real(M2u(x)*M2u(x) * (delu2g(x) + std::conj(delu2g(x)) + gam(x,dE)) )+
               std::real(M2u(x)*M2uz(x) * (delu2g(x) + std::conj(delu2z(x)) + gam(x,dE)) )+
               std::real(M2uz(x)*M2u(x) * (delu2z(x) + std::conj(delu2g(x)) + gam(x,dE)) )+
               std::real(M2uz(x)*M2uz(x) * (delu2z(x) + std::conj(delu2z(x)) + gam(x,dE)) )+

               //M3, Z

               std::real(M3t(x)*M3t(x) * (delt3g(x) + std::conj(delt3g(x)) + gam(x,dE)) )+
               std::real(M3t(x)*M3tz(x) * (delt3g(x) + std::conj(delt3z(x)) + gam(x,dE)) )+
               std::real(M3tz(x)*M3t(x) * (delt3z(x) + std::conj(delt3g(x)) + gam(x,dE)) )+
               std::real(M3tz(x)*M3tz(x) * (delt3z(x) + std::conj(delt3z(x)) + gam(x,dE)) )+

               //M2, Z, again - repeated since the unpolarized CS is (1/4)*Sum_lambda(polarized CS)
               std::real(M2u(x)*M2u(x) * (delu2g(x) + std::conj(delu2g(x)) + gam(x,dE)) )+
               std::real(M2u(x)*M2uz(x) * (delu2g(x) + std::conj(delu2z(x)) + gam(x,dE)) )+
               std::real(M2uz(x)*M2u(x) * (delu2z(x) + std::conj(delu2g(x)) + gam(x,dE)) )+
               std::real(M2uz(x)*M2uz(x) * (delu2z(x) + std::conj(delu2z(x)) + gam(x,dE)) )+

               //M3, Z, again

               std::real(M3t(x)*M3t(x) * (delt3g(x) + std::conj(delt3g(x)) + gam(x,dE)) )+
               std::real(M3t(x)*M3tz(x) * (delt3g(x) + std::conj(delt3z(x)) + gam(x,dE)) )+
               std::real(M3tz(x)*M3t(x) * (delt3z(x) + std::conj(delt3g(x)) + gam(x,dE)) )+
               std::real(M3tz(x)*M3tz(x) * (delt3z(x) + std::conj(delt3z(x)) + gam(x,dE)) )


           );
    }

//Construct the Tree-Level Cross Section
double tree_cs(double x)
    {
    return 0.5*pow(8.0*pi,-2)*M2(x)*pow(Ecm,-2);
    }

//Construct the Soft-Brehmsstralung-Corrected Cross-Section
double mCSfunc(double x, double dE)
    {
    //Exponentiating: CS_soft = CS_tree x exp(delta), with delta = soft correction / CS_tree
    //Instead of 1 + delta, it is exp(delta), to account for multiple soft photons
    return 2.0*pi*sin(x)*Lumi*pow(1.97e-11,2)*tree_cs(x)*exp(corr_soft(x,dE)/tree_cs(x));
    }



///////////////////////////////////////////////////////////////////
///HARD BREHMSSTRALUNG CROSS SECTION: Petriello, 2003
///////////////////////////////////////////////////////////////////

//Kinematic Definitions
//q_subscript refers to the frame of the q1+q2 system,
//relative to the CoM frame

double Eq0(double Ek)
    {
    return 0.5*sqrt(Ecm*(Ecm-2.*Ek));
    }
double q0(double Ek)
    {
    return sqrt(pow(Eq0(Ek),2.)-pow(me,2.));
    }

double betaq(double Ek)
    {
    return Ek/(Ecm-Ek);
    }
double gammaq(double Ek)
    {
    return pow(1.-betaq(Ek)*betaq(Ek),-0.5);
    }

//beta components of q1+q2 frame
double betaqx(double Ek, double tk)
    {
    return betaq(Ek)*sin(tk)*cos(0);
    }

double betaqy(double Ek, double tk)
    {
    return betaq(Ek)*sin(tk)*sin(0);
    }

double betaqz(double Ek, double tk)
    {
    return betaq(Ek)*cos(tk);
    }

//q1+q2 rest frame vector quantities
double q01x(double Ek, double tqr, double pqr)
    {
    return q0(Ek)*sin(tqr)*cos(pqr);
    }

double q01y(double Ek, double tqr, double pqr)
    {
    return q0(Ek)*sin(tqr)*sin(pqr);
    }

double q01z(double Ek, double tqr)
    {
    return q0(Ek)*cos(tqr);
    }

double q02x(double Ek, double tqr, double pqr)
    {
    return -q01x(Ek,tqr,pqr);
    }

double q02y(double Ek, double tqr, double pqr)
    {
    return -q01y(Ek,tqr,pqr);
    }

double q02z(double Ek, double tqr)
    {
    return -q01z(Ek,tqr);
    }


///////////////////////////////////////////////////////////////////
//Do Lorentz transformation to CoM frame and define CoM quantities
///////////////////////////////////////////////////////////////////

double Eq1cm(double Ek, double tk, double tqr, double pqr)
    {
    return gammaq(Ek)*(Eq0(Ek)-betaqx(Ek,tk)*q01x(Ek,tqr,pqr)-
                       betaqy(Ek,tk)*q01y(Ek,tqr,pqr)-betaqz(Ek,tk)*q01z(Ek,tqr));
    }

double Eq2cm(double Ek, double tk, double tqr, double pqr)
    {
    return gammaq(Ek)*(Eq0(Ek)-betaqx(Ek,tk)*q02x(Ek,tqr,pqr)-
                       betaqy(Ek,tk)*q02y(Ek,tqr,pqr)-betaqz(Ek,tk)*q02z(Ek,tqr));
    }


double Pxq1cm(double Ek, double tk, double tqr, double pqr)
    {
    return -gammaq(Ek)*betaqx(Ek, tk)*Eq0(Ek)
           +q01x(Ek, tqr, pqr)*(1.+(gammaq(Ek)-1)*pow(betaqx(Ek,tk),2.)/pow(betaq(Ek),2.))
           + q01y(Ek, tqr, pqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqy(Ek,tk)/pow(betaq(Ek),2.)
           +q01z(Ek,tqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.);
    }

double Pyq1cm(double Ek, double tk, double tqr, double pqr)
    {
    return -gammaq(Ek)*betaqy(Ek, tk)*Eq0(Ek)
           + q01x(Ek, tqr, pqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqy(Ek,tk)/pow(betaq(Ek),2.)
           +q01y(Ek, tqr, pqr)*(1.+(gammaq(Ek)-1)*pow(betaqy(Ek,tk),2.)/pow(betaq(Ek),2.))
           +q01z(Ek,tqr)*(gammaq(Ek)-1.)*betaqy(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.);
    }


double Pzq1cm(double Ek, double tk, double tqr, double pqr)
    {
    return -gammaq(Ek)*betaqz(Ek, tk)*Eq0(Ek)
           + q01x(Ek, tqr, pqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.)
           +q01y(Ek,tqr,pqr)*(gammaq(Ek)-1.)*betaqy(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.)
           +q01z(Ek, tqr)*(1.+(gammaq(Ek)-1)*pow(betaqz(Ek,tk),2.)/pow(betaq(Ek),2.));

    }


double Prq1cm(double Ek, double tk, double tqr, double pqr)
    {
    return sqrt(pow(Pxq1cm(Ek,tk,tqr,pqr),2.)+pow(Pyq1cm(Ek,tk,tqr,pqr),2.));

    }

double Pxq2cm(double Ek, double tk, double tqr, double pqr)
    {
    return -gammaq(Ek)*betaqx(Ek, tk)*Eq0(Ek)
           +q02x(Ek, tqr, pqr)*(1.+(gammaq(Ek)-1)*pow(betaqx(Ek,tk),2.)/pow(betaq(Ek),2.))
           + q02y(Ek, tqr, pqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqy(Ek,tk)/pow(betaq(Ek),2.)
           +q02z(Ek,tqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.);
    }

double Pyq2cm(double Ek, double tk, double tqr, double pqr)
    {
    return -gammaq(Ek)*betaqy(Ek, tk)*Eq0(Ek)
           + q02x(Ek, tqr, pqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqy(Ek,tk)/pow(betaq(Ek),2.)
           +q02y(Ek, tqr, pqr)*(1.+(gammaq(Ek)-1)*pow(betaqy(Ek,tk),2.)/pow(betaq(Ek),2.))
           +q02z(Ek,tqr)*(gammaq(Ek)-1.)*betaqy(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.);
    }


double Pzq2cm(double Ek, double tk, double tqr, double pqr)
    {
    return -gammaq(Ek)*betaqz(Ek, tk)*Eq0(Ek)
           + q02x(Ek, tqr, pqr)*(gammaq(Ek)-1.)*betaqx(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.)
           +q02y(Ek,tqr,pqr)*(gammaq(Ek)-1.)*betaqy(Ek,tk)*betaqz(Ek,tk)/pow(betaq(Ek),2.)
           +q02z(Ek, tqr)*(1.+(gammaq(Ek)-1)*pow(betaqz(Ek,tk),2.)/pow(betaq(Ek),2.));

    }

double Prq2cm(double Ek, double tk, double tqr, double pqr)
    {
    return sqrt(pow(Pxq2cm(Ek,tk,tqr,pqr),2.)+pow(Pyq2cm(Ek,tk,tqr,pqr),2.));

    }


///////////////////////////////////////////////////////////////////
//Modified (inelastic) Mandelstam variables, for Hard Brehm CS
//See Petriello's paper for full definitions
///////////////////////////////////////////////////////////////////


double sv(double Ek, double tk, double tqr, double pqr)
    {
    return Ecm*Ecm;
    }
double tv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(Ecm/2.-Eq1cm(Ek,tk,tqr,pqr),2.)-
           pow(Prq1cm(Ek,tk,tqr,pqr),2.)-pow(Pcm-Pzq1cm(Ek,tk,tqr,pqr),2.);
    }
double uv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(Ecm/2.-Eq2cm(Ek,tk,tqr,pqr),2.)-
           pow(Prq2cm(Ek,tk,tqr,pqr),2.)-pow(Pcm-Pzq2cm(Ek,tk,tqr,pqr),2.);
    }

double sp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(Eq1cm(Ek,tk,tqr,pqr)+Eq2cm(Ek,tk,tqr,pqr),2.)-
           pow(Pxq1cm(Ek,tk,tqr,pqr)+Pxq2cm(Ek,tk,tqr,pqr),2.)-
           pow(Pyq1cm(Ek,tk,tqr,pqr)+Pyq2cm(Ek,tk,tqr,pqr),2.)-
           pow(Pzq1cm(Ek,tk,tqr,pqr)+Pzq2cm(Ek,tk,tqr,pqr),2.);
    }
double tp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(Ecm/2.-Eq2cm(Ek,tk,tqr,pqr),2.)-
           pow(Prq2cm(Ek,tk,tqr,pqr),2.)-pow(-Pcm-Pzq2cm(Ek,tk,tqr,pqr),2.);
    }
double up(double Ek, double tk, double tqr, double pqr)
    {
    return pow(Ecm/2.-Eq1cm(Ek,tk,tqr,pqr),2.)-
           pow(Prq1cm(Ek,tk,tqr,pqr),2.)-pow(-Pcm-Pzq1cm(Ek,tk,tqr,pqr),2.);
    }


double d1(double Ek, double tk, double tqr, double pqr)
    {
    return -0.5/(Ek*Ecm/2.-Ek*cos(tk)*Pcm);
    }
double d2(double Ek, double tk, double tqr, double pqr)
    {
    return -0.5/(Ek*Ecm/2.+Ek*cos(tk)*Pcm);
    }
double d3(double Ek, double tk, double tqr, double pqr)
    {
    return 0.5/(Ek*Eq1cm(Ek,tk,tqr,pqr)-Ek*cos(tk)
                *Pzq1cm(Ek,tk,tqr,pqr)-Ek*sin(tk)*Pxq1cm(Ek,tk,tqr,pqr));
    }
double d4(double Ek, double tk, double tqr, double pqr)
    {
    return 0.5/(Ek*Eq2cm(Ek,tk,tqr,pqr)-Ek*cos(tk)
                *Pzq2cm(Ek,tk,tqr,pqr)-Ek*sin(tk)*Pxq2cm(Ek,tk,tqr,pqr));
    }

///////////////////////////////////////////////////////////////////
//  Additional relations in Petriello's Paper
///////////////////////////////////////////////////////////////////

double cllsv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./sv(Ek,tk,tqr,pqr)+
                       pow(gv-ga,2.)/(sw2*cw2*(sv(Ek,tk,tqr,pqr)-mz2)));
    }
double crrsv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./sv(Ek,tk,tqr,pqr)+
                       pow(gv+ga,2.)/(sw2*cw2*(sv(Ek,tk,tqr,pqr)-mz2)));
    }
double clrsv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./sv(Ek,tk,tqr,pqr)+
                       (pow(gv,2.)-pow(ga,2.))/(sw2*cw2*(sv(Ek,tk,tqr,pqr)-mz2)));
    }


double clltv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./tv(Ek,tk,tqr,pqr)+
                       pow(gv-ga,2.)/(sw2*cw2*(tv(Ek,tk,tqr,pqr)-mz2)));
    }
double crrtv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./tv(Ek,tk,tqr,pqr)+
                       pow(gv+ga,2.)/(sw2*cw2*(tv(Ek,tk,tqr,pqr)-mz2)));
    }
double clrtv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./tv(Ek,tk,tqr,pqr)+
                       (pow(gv,2.)-pow(ga,2.))/(sw2*cw2*(tv(Ek,tk,tqr,pqr)-mz2)));
    }



double clluv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./uv(Ek,tk,tqr,pqr)+
                       pow(gv-ga,2.)/(sw2*cw2*(uv(Ek,tk,tqr,pqr)-mz2)));
    }
double crruv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./uv(Ek,tk,tqr,pqr)+
                       pow(gv+ga,2.)/(sw2*cw2*(uv(Ek,tk,tqr,pqr)-mz2)));
    }
double clruv(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./uv(Ek,tk,tqr,pqr)+
                       (pow(gv,2.)-pow(ga,2.))/(sw2*cw2*(uv(Ek,tk,tqr,pqr)-mz2)));
    }



double cllsp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./sp(Ek,tk,tqr,pqr)+
                       pow(gv-ga,2.)/(sw2*cw2*(sp(Ek,tk,tqr,pqr)-mz2)));
    }
double crrsp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./sp(Ek,tk,tqr,pqr)+
                       pow(gv+ga,2.)/(sw2*cw2*(sp(Ek,tk,tqr,pqr)-mz2)));
    }
double clrsp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./sp(Ek,tk,tqr,pqr)+
                       (pow(gv,2.)-pow(ga,2.))/(sw2*cw2*(sp(Ek,tk,tqr,pqr)-mz2)));
    }



double clltp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./tp(Ek,tk,tqr,pqr)+
                       pow(gv-ga,2.)/(sw2*cw2*(tp(Ek,tk,tqr,pqr)-mz2)));
    }
double crrtp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./tp(Ek,tk,tqr,pqr)+
                       pow(gv+ga,2.)/(sw2*cw2*(tp(Ek,tk,tqr,pqr)-mz2)));
    }
double clrtp(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./tp(Ek,tk,tqr,pqr)+
                       (pow(gv,2.)-pow(ga,2.))/(sw2*cw2*(tp(Ek,tk,tqr,pqr)-mz2)));
    }



double cllup(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./up(Ek,tk,tqr,pqr)+
                       pow(gv-ga,2.)/(sw2*cw2*(up(Ek,tk,tqr,pqr)-mz2)));
    }
double crrup(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./up(Ek,tk,tqr,pqr)+
                       pow(gv+ga,2.)/(sw2*cw2*(up(Ek,tk,tqr,pqr)-mz2)));
    }
double clrup(double Ek, double tk, double tqr, double pqr)
    {
    return pow(ec,2.)*(1./up(Ek,tk,tqr,pqr)+
                       (pow(gv,2.)-pow(ga,2.))/(sw2*cw2*(up(Ek,tk,tqr,pqr)-mz2)));
    }



///////////////////////////////////////////////////////////////////
//  Below are the (lengthy) brehm matrix elements, from the appendix
//  of Petriello's paper.
///////////////////////////////////////////////////////////////////

double Mllha2(double Ek, double tk, double tqr, double pqr)   //new
    {
    return 8.*ec*ec*(
               (sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*
                sp(Ek,tk,tqr,pqr))*(tv(Ek,tk,tqr,pqr)*pow(clltv(Ek,tk,tqr,pqr),2.)*
                                    d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr)*pow(clluv(Ek,tk,tqr,pqr),2.)
                                    *d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)*pow(clltp(Ek,tk,tqr,pqr),2.)*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr)*pow(cllup(Ek,tk,tqr,pqr),2.)*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr))
               -2.*sp(Ek,tk,tqr,pqr)*(clltp(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)+clltv(Ek,tk,tqr,pqr)*clluv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr))
               -2.*sv(Ek,tk,tqr,pqr)*(clltp(Ek,tk,tqr,pqr)*clluv(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)+clltv(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr))
               -2.*(clltp(Ek,tk,tqr,pqr)+cllup(Ek,tk,tqr,pqr))*(clltv(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr))*sp(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*(tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
               -2.*(clltp(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr))*(clltv(Ek,tk,tqr,pqr)+cllup(Ek,tk,tqr,pqr))*sv(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*(tv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
               -(clluv(Ek,tk,tqr,pqr)*clltp(Ek,tk,tqr,pqr)+clltp(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr))
               *(tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))-uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
               -(clltv(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr)+cllup(Ek,tk,tqr,pqr)*clltp(Ek,tk,tqr,pqr)+clltv(Ek,tk,tqr,pqr)*clltp(Ek,tk,tqr,pqr))
               *(uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))-tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
               -(clluv(Ek,tk,tqr,pqr)*clltp(Ek,tk,tqr,pqr)+clltv(Ek,tk,tqr,pqr)*clluv(Ek,tk,tqr,pqr)+clltv(Ek,tk,tqr,pqr)*clltp(Ek,tk,tqr,pqr))
               *(uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(up(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))-tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
               -(clltv(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr)*clltv(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr)*cllup(Ek,tk,tqr,pqr))
               *(tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))-uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));
    }



double Mrrha2(double Ek, double tk, double tqr, double pqr)   //new
    {
    return 8.*ec*ec*(
               (sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr))*(tv(Ek,tk,tqr,pqr)*pow(crrtv(Ek,tk,tqr,pqr),2.)*d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr)*pow(crruv(Ek,tk,tqr,pqr),2.)
                       *d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)*pow(crrtp(Ek,tk,tqr,pqr),2.)*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr)*pow(crrup(Ek,tk,tqr,pqr),2.)*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr))
               -2.*sp(Ek,tk,tqr,pqr)*(crrtp(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)+crrtv(Ek,tk,tqr,pqr)*crruv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr))
               -2.*sv(Ek,tk,tqr,pqr)*(crrtp(Ek,tk,tqr,pqr)*crruv(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)+crrtv(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr))
               -2.*(crrtp(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr))*(crrtv(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr))*sp(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*(tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
               -2.*(crrtp(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr))*(crrtv(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr))*sv(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*(tv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
               -(crruv(Ek,tk,tqr,pqr)*crrtp(Ek,tk,tqr,pqr)+crrtp(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr))
               *(tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))-uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
               -(crrtv(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr)*crrtp(Ek,tk,tqr,pqr)+crrtv(Ek,tk,tqr,pqr)*crrtp(Ek,tk,tqr,pqr))
               *(uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))-tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
               -(crruv(Ek,tk,tqr,pqr)*crrtp(Ek,tk,tqr,pqr)+crrtv(Ek,tk,tqr,pqr)*crruv(Ek,tk,tqr,pqr)+crrtv(Ek,tk,tqr,pqr)*crrtp(Ek,tk,tqr,pqr))
               *(uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(up(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))-tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
               -(crrtv(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr)*crrtv(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr)*crrup(Ek,tk,tqr,pqr))
               *(tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr))-sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))-uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)))*d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));
    }



double Mlrha2(double Ek, double tk, double tqr, double pqr)
    {
    return 8.*ec*ec*(uv(Ek,tk,tqr,pqr)*pow(clruv(Ek,tk,tqr,pqr),2.)*(pow(tv(Ek,tk,tqr,pqr),2.)+pow(tp(Ek,tk,tqr,pqr),2.))*d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)*pow(clrtv(Ek,tk,tqr,pqr),2.)*(pow(uv(Ek,tk,tqr,pqr),2.)+pow(up(Ek,tk,tqr,pqr),2.))*d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
                     +tp(Ek,tk,tqr,pqr)*pow(clrtp(Ek,tk,tqr,pqr),2.)*(sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)-2.*tp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)-2.*tp(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+2.*sp(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
                     +up(Ek,tk,tqr,pqr)*pow(clrup(Ek,tk,tqr,pqr),2.)*(sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)-2.*up(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)-2.*up(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+2.*sp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
                     +(clrtv(Ek,tk,tqr,pqr)*clrtp(Ek,tk,tqr,pqr)*((uv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*(sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))+2.*sv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))+clruv(Ek,tk,tqr,pqr)*clrup(Ek,tk,tqr,pqr)*((tv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*(sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr))+2.*sv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)))*d1(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
                     +(clrtv(Ek,tk,tqr,pqr)*clrtp(Ek,tk,tqr,pqr)*((uv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*(sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))+2.*sp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))+clruv(Ek,tk,tqr,pqr)*clrup(Ek,tk,tqr,pqr)*((tv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*(sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr))+2.*sp(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)))*d3(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)
                     +2.*clruv(Ek,tk,tqr,pqr)*clrup(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+2.*clrtv(Ek,tk,tqr,pqr)*clrtp(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)+2.*clrtv(Ek,tk,tqr,pqr)*clrtp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
                     +2.*clruv(Ek,tk,tqr,pqr)*clrup(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));
    }





double Mllhb2(double Ek, double tk, double tqr, double pqr)
    {
    return 8.*ec*ec*me*(me/se)*(
               -pow(clltp(Ek,tk,tqr,pqr)+cllup(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+pow(tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr),2.))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
               +pow(clrtp(Ek,tk,tqr,pqr),2.)*up(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
               +pow(clrup(Ek,tk,tqr,pqr),2.)*tp(Ek,tk,tqr,pqr)*(up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
               -pow(clltv(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+pow(tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr),2.))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
               +pow(clrtv(Ek,tk,tqr,pqr),2.)*uv(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
               +pow(clruv(Ek,tk,tqr,pqr),2.)*tv(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
               +2.*pow(clluv(Ek,tk,tqr,pqr)+clltp(Ek,tk,tqr,pqr),2.)*sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
               +2.*pow(clltv(Ek,tk,tqr,pqr)+cllup(Ek,tk,tqr,pqr),2.)*sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));

    }


double Mrrhb2(double Ek, double tk, double tqr, double pqr)
    {
    return 8.*ec*ec*me*me/sv(Ek,tk,tqr,pqr)*(-pow(crrtp(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+pow(tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr),2.))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)+pow(clrtp(Ek,tk,tqr,pqr),2.)*up(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            +pow(clrup(Ek,tk,tqr,pqr),2.)*tp(Ek,tk,tqr,pqr)*(up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-uv(Ek,tk,tqr,pqr)-tv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)-pow(crrtv(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)+pow(tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr),2.))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)+pow(clrtv(Ek,tk,tqr,pqr),2.)*uv(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr))
                    +sv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)+pow(clruv(Ek,tk,tqr,pqr),2.)*tv(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)-up(Ek,tk,tqr,pqr)-tp(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+2.*sv(Ek,tk,tqr,pqr)*sp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            +2.*pow(crruv(Ek,tk,tqr,pqr)+crrtp(Ek,tk,tqr,pqr),2.)*sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+2.*pow(crrtv(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr),2.)*sv(Ek,tk,tqr,pqr)*sv(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));
    }



double Mlrhb2(double Ek, double tk, double tqr, double pqr)
    {
    return  8.*ec*ec*me*me/sv(Ek,tk,tqr,pqr)*(pow(crrtp(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*pow(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr),2.)*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            -pow(clrtp(Ek,tk,tqr,pqr),2.)*up(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            -pow(clrup(Ek,tk,tqr,pqr),2.)*tp(Ek,tk,tqr,pqr)*(up(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            +pow(clltv(Ek,tk,tqr,pqr)+clluv(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*pow(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr),2.)*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            -pow(clrtv(Ek,tk,tqr,pqr),2.)*uv(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            -pow(clruv(Ek,tk,tqr,pqr),2.)*tv(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            +2.*pow(clruv(Ek,tk,tqr,pqr),2.)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+2.*pow(clrtp(Ek,tk,tqr,pqr),2.)*uv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
            +2.*pow(clrtv(Ek,tk,tqr,pqr),2.)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)+2.*pow(clrup(Ek,tk,tqr,pqr),2.)*tv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));
    }


double Mrlhb2(double Ek, double tk, double tqr, double pqr)
    {
    return  8.*ec*ec*me*me/sv(Ek,tk,tqr,pqr)*(pow(crrtp(Ek,tk,tqr,pqr)+crrup(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*pow(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr),2.)*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            -pow(clrtp(Ek,tk,tqr,pqr),2.)*up(Ek,tk,tqr,pqr)*(tp(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            -pow(clrup(Ek,tk,tqr,pqr),2.)*tp(Ek,tk,tqr,pqr)*(up(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d1(Ek,tk,tqr,pqr)
            +pow(crrtv(Ek,tk,tqr,pqr)+crruv(Ek,tk,tqr,pqr),2.)*sp(Ek,tk,tqr,pqr)*pow(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr),2.)*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            -pow(clrtv(Ek,tk,tqr,pqr),2.)*uv(Ek,tk,tqr,pqr)*(tv(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*up(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*uv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            -pow(clruv(Ek,tk,tqr,pqr),2.)*tv(Ek,tk,tqr,pqr)*(uv(Ek,tk,tqr,pqr)*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))+sv(Ek,tk,tqr,pqr)*tp(Ek,tk,tqr,pqr)+sp(Ek,tk,tqr,pqr)*tv(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d2(Ek,tk,tqr,pqr)
            +2.*pow(clruv(Ek,tk,tqr,pqr),2.)*tp(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)+2.*pow(clrtp(Ek,tk,tqr,pqr),2.)*uv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*d3(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)
            +2.*pow(clrtv(Ek,tk,tqr,pqr),2.)*up(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)+2.*pow(clrup(Ek,tk,tqr,pqr),2.)*tv(Ek,tk,tqr,pqr)*(sv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d4(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr));
    }






double Mhcunpol2(double Ek, double tk, double tqr, double pqr)
    {
    return 64.*pow(ec,6.)*me*me*((sv(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)/pow(tv(Ek,tk,tqr,pqr),2.)
                                 +(sv(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*d2(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)/pow(uv(Ek,tk,tqr,pqr),2.)
                                 +(sv(Ek,tk,tqr,pqr)+up(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+uv(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d3(Ek,tk,tqr,pqr)/pow(tp(Ek,tk,tqr,pqr),2.)
                                 +(sv(Ek,tk,tqr,pqr)+tp(Ek,tk,tqr,pqr))*(sp(Ek,tk,tqr,pqr)+tv(Ek,tk,tqr,pqr))*d1(Ek,tk,tqr,pqr)*d4(Ek,tk,tqr,pqr)/pow(up(Ek,tk,tqr,pqr),2.));
    }


double Mh2(double Ek, double tk, double tqr, double pqr)
    {
    return 0.25*(Mllha2(Ek,tk,tqr,pqr)+Mrrha2(Ek,tk,tqr,pqr)+2.*Mlrha2(Ek,tk,tqr,pqr)+Mllhb2(Ek,tk,tqr,pqr)+Mrrhb2(Ek,tk,tqr,pqr)+Mlrhb2(Ek,tk,tqr,pqr)+Mrlhb2(Ek,tk,tqr,pqr))+Mhcunpol2(Ek,tk,tqr,pqr);
    }



double dSigmahdEkdTkdTqr(double Ek , double tk, double tqr, double pqr)
    {
    return pow(1.97e-11,2.)*Lumi*sin(tk)*sin(tqr)*Ek*Mh2(Ek,tk,tqr,pqr)/(64.*sv(Ek,tk,tqr,pqr)*pow(2.*pi,4.));
    }
Double_t sqr(Double_t x)
    {
    return x*x;
    }


int Radiative_Moller_Gen()
    {
    cout<<"mllha2: "<<Mllha2(3.58757,2.16604,0.0119225,0)<<" mlrha2: "<<Mlrha2(3.58757,2.16604,0.0119225,0)<<" Mrrha2: "<<Mrrha2(3.58757,2.16604,0.0119225,0)<<" mllhb2: "<<Mllhb2(3.58757,2.16604,0.0119225,0)<<" mlrhb2: "<<Mlrhb2(3.58757,2.16604,0.0119225,0)<<" mrlhb2: "<<Mrlhb2(3.58757,2.16604,0.0119225,0)<<" mrrhb2: "<<Mrrhb2(3.58757,2.16604,0.0119225,0)<<" mhcunpol: "<<Mhcunpol2(3.58757,2.16604,0.0119225,0)<<endl;
    cout<<" Prq1 "<<Prq1cm(3.58757,2.16604,0.0119225,0)<<" Prq2 "<<Prq2cm(3.58757,2.16604,0.0119225,0)<<" Pzq1 "<<Pzq1cm(3.58757,2.16604,0.0119225,0)<<" Pzq2 "<<Pzq2cm(3.58757,2.16604,0.0119225,0)<<endl;

    //=========================================================
    long nEve   =     50000;   // Total MC statistics
    //=========================================================
    TH2D  *hst_xy = new TH2D("hst_xy" ,  "Scattered Electron Energy vs. Angle", 90,0,1,100,10000,48000 );
    TH2D *ptpz = new TH2D("ptpz", "Electron Pt vs Pz",102,0,50000,50,0,10000);
    TH1D *ptpzg = new TH1D("ptpzg", "Integrated Bin",25,47500,48000);
    TH2D *aa = new TH2D("aa","e1 Angle vs e2 Angle",180,0,90,180,0,90);
    TH2D *pp = new TH2D("pp","e1 Momentum vs e2 Momentum",199,0.5,50000,199,0.5,50000);
    TH2D *eg = new TH2D("eg","e1 Angle vs Photon Angle",360,0,180,180,0,90);
    TH1D *kk = new TH1D("kk","Ek distribution",50,0,38000);
    TH1D *CSint = new TH1D("CSint","Photon ",100,0.004,0.008);
    TH1D *w_int = new TH1D("w_int","Total weight",5,0,5);


    double dE = 1e-4*sqrt(se);
    double EkMax = (Ecm*Ecm-4.*me*me)/(2.*Ecm);
    double tkCut = 0;
    double tqrCut = 0;

    TCanvas *cplot = new TCanvas("cplot","Canvas for plotting 1",800,800);
    cplot->cd();
//    double c = 0;
//
//    TH2D *cseval = new TH2D("cseval","CS Slice",100,0,pi,100,0,pi);
//    for (int i =0;i<100;i++){
//        for(int j = 0;j<100;j++){
//            cseval->SetBinContent(i,i,dSigmahdEkdTkdTqr(3.58757,i*pi/100., j*pi/100.));
//        }
//    }
    TF2 *fa3 = new TF2("fa3","dSigmahdEkdTkdTqr(3.58757, x, y,0)",0,pi,0,pi);
//
    fa3->Draw("colz");
    cplot->SetLogz();

    hst_xy->Sumw2();
    ptpz->Sumw2();
    ptpzg->Sumw2();
    aa->Sumw2();
    pp->Sumw2();
    eg->Sumw2();
    kk->Sumw2();
    CSint->Sumw2();
    w_int->Sumw2();

    gStyle->SetOptStat(1000010);

    hst_xy->SetXTitle("Scattered Electron Angle");
    hst_xy->SetYTitle("Scattered Electron Energy");

    ptpz->SetXTitle("Pz");
    ptpz->SetYTitle("Pt");

    aa->SetXTitle("e1 Angle");
    aa->SetYTitle("e2 Angle");

    pp->SetXTitle("e1 Momentum");
    pp->SetYTitle("e2 Momentum");

    eg->SetYTitle("e1 Angle");
    eg->SetXTitle("Photon Angle");

    kk->SetXTitle("Photon Energy [MeV]");



    TH1D *ekDist = new TH1D("ekDist","Ek Distribution",1000,dE,EkMax);
    for (int i = 0; i<ekDist->GetNbinsX(); i++)
        {
        ekDist->SetBinContent(i,1./(i+1.));
        }
    ekDist->Scale(1./ekDist->Integral("width"));


    TH1D *tkDist = new TH1D("tkDist","Theta K Distribution",1000,tkCut,pi-tkCut);
    TH1D *tqrDist = new TH1D("tqrDist","Theta K Distribution",1000,tqrCut,pi-tqrCut);

    for (int i = 0; i<tkDist->GetNbinsX(); i++)
        {
        tkDist->SetBinContent(i,1./(sqrt(pow(pi/2.,2.)-pow((i/1000.)*pi-pi/2.,2.))));
        }
    tkDist->Scale(1./tkDist->Integral("width"));

    for (int i = 0; i<tqrDist->GetNbinsX(); i++)
        {
        tqrDist->SetBinContent(i,1./(sqrt(pow(pi/2.,2.)-pow((i/1000.)*pi-pi/2.,2.))));
        }
    tqrDist->Scale(1./tqrDist->Integral("width"));

//    tqrDist->Draw();
//    cplot->SetLogy();

    TRandom *randGen   = new TRandom3();  // Create random number generator
    randGen->SetSeed(0);
    //=========================================================
    //======================================================================
    TCanvas *cKanwa = new TCanvas("cKanwa","Canvas for plotting",1350,800);
    cKanwa->Divide(4,2);
    cKanwa->cd();
    int nshow = 500;
    for(long loop=0; loop<nEve; loop++)
        {

        double nEve_f = (double) nEve;


        double xeCut = 0.001;
        double pqr = twopi*randGen->Uniform();
        double weight;

        double Ek=ekDist->GetRandom();//dE+(EkMax-dE)*PseRan->Uniform(); //Must be less than 5.016
        double tk=tkCut+(pi-tkCut)*randGen->Uniform();//tkDist->GetRandom();//tkCut+(pi-tkCut)*PseRan->Uniform();
        double tqr = tqrCut+(pi-tqrCut)*randGen->Uniform();//tqrDist->GetRandom();//tqrCut+(pi-tqrCut)*PseRan->Uniform();

        double ekWeight = 1./ekDist->GetBinContent(ekDist->FindBin(Ek));//replaces range of Ek
        double tkWeight = pi-2.*tkCut;//1./tkDist->GetBinContent(tkDist->FindBin(tk));//replaces range of tk
        double tqrWeight = pi-2.*tqrCut;//1./tqrDist->GetBinContent(tqrDist->FindBin(tqr));//replaces range of tk

        double pqrWeight = twopi;

        double phik = 0.;
        double xe = xeCut+(pi-xeCut)*randGen->Uniform(); //Elastic Angle
        double tmin = 0.00465;
        double tmax = 0.008;
        double Ecut = 10000.;
        double pickProc = randGen->Uniform();


        TLorentzVector *cm = new TLorentzVector(0.,0.,Pbeam,Ebeam+me);


        if (pickProc<0.5)
            {
            TLorentzVector *kcm = new TLorentzVector(Ek*sin(tk)*cos(phik),Ek*sin(tk)*sin(phik),Ek*cos(tk),Ek);

            TLorentzVector *qcm = new TLorentzVector(-Ek*sin(tk)*cos(phik),-Ek*sin(tk)*sin(phik),-Ek*cos(tk),Ecm-Ek);
            TLorentzVector *qcmBoost = new TLorentzVector(*qcm);

            TLorentzVector *qr = new TLorentzVector(*qcm);
            qr->Boost(-qcm->BoostVector());
//            cout<<"qrE "<<qr->E()<<endl;
//            cout<<"qcmE "<<qcm->E()<<endl;
//            cout<<"Ek "<<kcm->E()<<endl;

            double pqcm = sqrt(pow(qr->E()/2.,2.)-me*me);

            TLorentzVector *q1r = new TLorentzVector(pqcm*sin(tqr)*cos(pqr),pqcm*sin(tqr)*sin(pqr),pqcm*cos(tqr),qr->E()/2.);
            TLorentzVector *q2r = new TLorentzVector(-pqcm*sin(tqr)*cos(pqr),-pqcm*sin(tqr)*sin(pqr),-pqcm*cos(tqr),qr->E()/2.);

            TLorentzVector *q1cm = new TLorentzVector(*q1r);
            TLorentzVector *q2cm = new TLorentzVector(*q2r);
            q1cm->Boost(qcm->BoostVector());
            q2cm->Boost(qcm->BoostVector());


//            TLorentzVector *q1cm = new TLorentzVector(Prq1cm(Ek,tk,tqr)*cos(phik),Prq1cm(Ek,tk,tqr)*sin(phik),Pzq1cm(Ek,tk,tqr),Eq1cm(Ek,tk,tqr));
//            TLorentzVector *q2cm = new TLorentzVector(Prq2cm(Ek,tk,tqr)*cos(phik),Prq2cm(Ek,tk,tqr)*sin(phik),Pzq2cm(Ek,tk,tqr),Eq2cm(Ek,tk,tqr));
//
//            //Do rotation in rest frame of q1+q2
//            TLorentzVector *q = new TLorentzVector(*q1cm+*q2cm);
//            q1cm->Boost(-q->BoostVector());
//            q2cm->Boost(-q->BoostVector());
//            q1cm->RotateZ(pqr);
//            q2cm->RotateZ(pqr);
//            q1cm->Boost(q->BoostVector());
//            q2cm->Boost(q->BoostVector());



            //cout<<kcm->Pz()+q1cm->Pz()+q2cm->Pz()<<endl;

            TLorentzVector *q1 = new TLorentzVector(*q1cm);
            TLorentzVector *q2 = new TLorentzVector(*q2cm);
            TLorentzVector *k = new TLorentzVector(*kcm);
            q1->Boost(cm->BoostVector());
            q2->Boost(cm->BoostVector());
            k->Boost(cm->BoostVector());
//            cout<<"q1 E "<<q1->E()<<endl;
//            cout<<"q2 E "<<q2->E()<<endl;
//            cout<<"k E "<<k->E()<<endl;

            weight = 2.*dSigmahdEkdTkdTqr(Ek,tk,tqr,pqr)*(1./nEve_f)*ekWeight*tkWeight*tqrWeight*pqrWeight;
            if (weight<0)
                {
                cout<<"weight: "<<weight<<" cs: "<<dSigmahdEkdTkdTqr(Ek,tk,tqr,pqr)<<" Ek: "<<Ek<<" tk: "<<tk<<" tqr: "<<tqr<<" pqr: "<<pqr<<endl;
                }
            if (q1->Theta() > tmin )
                {
                if(q1->Theta() < tmax)
                    {
                    if(q1->E() > Ecut)
                        {

                        hst_xy->Fill(q1->Theta()*180./pi,q1->E(),weight);
                        //hst_xy->Fill(q2->Theta()*180./pi,q2->E(),weight);
                        aa->Fill(q1->Theta()*180./pi,q2->Theta()*180./pi,weight);
                        pp->Fill(q1->P(),q2->P(),weight);
                        ptpz->Fill(q1->Pz(),q1->Pt(),weight);
                        //ptpz->Fill(q2->Pz(),q2->Pt(),weight);
                        ptpzg->Fill(q1->Theta(),weight);
                        //cout<<"q1 E "<<q1->E()<<endl;
                        eg->Fill(k->Theta()*180./pi,q1->Theta()*180./pi,weight);
                        CSint->Fill(q1->Theta(),weight);
                        kk->Fill(k->E());
                        w_int->Fill(1,weight);
                        }
                    }
                }

            if (q2->Theta() > tmin )
                {
                if(q2->Theta() < tmax)
                    {
                    if(q2->E() > Ecut)
                        {

                        //hst_xy->Fill(q1->Theta()*180./pi,q1->E(),weight);
                        hst_xy->Fill(q2->Theta()*180./pi,q2->E(),weight);
                        aa->Fill(q1->Theta()*180./pi,q2->Theta()*180./pi,weight);
                        pp->Fill(q1->P(),q2->P(),weight);
                        ptpz->Fill(q1->Pz(),q1->Pt(),weight);
                        //ptpz->Fill(q2->Pz(),q2->Pt(),weight);
                        ptpzg->Fill(q2->Theta(),weight);
                        eg->Fill(k->Theta()*180./pi,q1->Theta()*180./pi,weight);
                        CSint->Fill(q2->Theta(),weight);
                        kk->Fill(k->E());
                        w_int->Fill(1,weight);
                        }
                    }
                }



            }
        if (pickProc >0.5)
            {

            weight = 2.*mCSfunc(xe,dE)/nEve*(pi-2.*xeCut);

            TLorentzVector *q1cm = new TLorentzVector(Pcmp*sin(xe)*cos(phik),Pcmp*sin(xe)*sin(phik),Pcmp*cos(xe),Ecmp);
            TLorentzVector *q2cm = new TLorentzVector(-Pcmp*sin(xe)*cos(phik),-Pcmp*sin(xe)*sin(phik),-Pcmp*cos(xe),Ecmp);

            TLorentzVector *q1 = new TLorentzVector(*q1cm);
            TLorentzVector *q2 = new TLorentzVector(*q2cm);

            q1->Boost(cm->BoostVector());
            q2->Boost(cm->BoostVector());

            if (q1->Theta() > tmin )
                {
                if(q1->Theta() < tmax)
                    {
                    if(q1->E() > Ecut)
                        {
                        hst_xy->Fill(q1->Theta()*180./pi,q1->E(),weight);
                        ptpz->Fill(q1->Pz(),q1->Pt(),weight);
                        //hst_xy->Fill(q2->Theta()*180./pi,q2->E(),weight);
                        //ptpz->Fill(q2->Pz(),q2->Pt(),weight);
                        aa->Fill(q1->Theta()*180./pi,q2->Theta()*180./pi,weight);
                        pp->Fill(q1->P(),q2->P(),weight);
                        CSint->Fill(q1->Theta(),weight);
                        w_int->Fill(1,weight);
                        }
                    }
                }

            if (q2->Theta() > tmin )
                {
                if(q2->Theta() < tmax)
                    {
                    if(q2->E() > Ecut)
                        {

                        //hst_xy->Fill(q1->Theta()*180./pi,q1->E(),weight);
                        //ptpz->Fill(q1->Pz(),q1->Pt(),weight);
                        hst_xy->Fill(q2->Theta()*180./pi,q2->E(),weight);
                        ptpz->Fill(q2->Pz(),q2->Pt(),weight);
                        aa->Fill(q1->Theta()*180./pi,q2->Theta()*180./pi,weight);
                        pp->Fill(q1->P(),q2->P(),weight);
                        CSint->Fill(q2->Theta(),weight);
                        w_int->Fill(1,weight);
                        }
                    }
                }

            }

        //	  if (loop<40){
        //		  cout<<"E1 Theta "<<q1->Theta()<<" E1 E "<<q1->E()<<" E2 Theta "<<q2->Theta()<<" E2 E "<<q2->E()<<" k Theta "<<k->Theta()<<" E_k "<<k->E()<<endl;}

        if(loop == nshow)
            {
            nshow += 500;
            double loopd = (double) loop;
//            itgrl = 0;
//            err = 0;
//            for(int i=0;i<CSint->GetNbinsX();i++){
//                itgrl+= CSint->GetBinContent(i);
//                err += pow(CSint->GetBinError(i),2.);
//            }
//            cout<<"integral "<<itgrl*nEve/loop<<" err "<<sqrt(err)*nEve/loop<<endl;
            cout<<"integral "<<w_int->GetBinContent(2)*nEve/loopd<<" err "<<w_int->GetBinError(2)*nEve/loopd<<endl;

            cKanwa->cd(1);
            gPad->SetLogz();
            gPad->SetLogy();
            hst_xy->Draw("colz");//"lego2");

            cKanwa->cd(2);
            gPad->SetLogz();
            ptpz->Draw("colz");//"lego2");

            cKanwa->cd(3);
            gPad->SetLogz();
            aa->Draw("colz");

            cKanwa->cd(4);
            gPad->SetLogz();
            pp->Draw("colz");

            cKanwa->cd(5);
            gPad->SetLogy();
            ptpzg->Draw();

            cKanwa->cd(6);
            gPad->SetLogz();
            eg->Draw("colz");

            cKanwa->cd(7);
            kk->Draw();

            cKanwa->cd(8);
            w_int->Draw();

            cKanwa->Update();
            }

        if( ((loop)%100000)==0 )
            {
            cout<<"   loop= "<<loop<<endl;
            }
        }
    cout<<"integral "<<w_int->GetBinContent(2)<<" err "<<w_int->GetBinError(2)<<endl;

    cKanwa->cd(1);
    gPad->SetLogz();
    gPad->SetLogy();
    hst_xy->Draw("colz");//"lego2");

    cKanwa->cd(2);
    gPad->SetLogz();
    ptpz->Draw("colz");//"lego2");

    cKanwa->cd(3);
    gPad->SetLogz();
    aa->Draw("colz");

    cKanwa->cd(4);
    gPad->SetLogz();
    pp->Draw("colz");

    cKanwa->cd(5);
    gPad->SetLogy();
    ptpzg->Draw();

    cKanwa->cd(6);
    gPad->SetLogz();
    eg->Draw("colz");

    cKanwa->cd(7);
    kk->Draw();

    cKanwa->cd(8);
    w_int->Draw();


    cKanwa->Update();

    return 0;
    } // end of Demo

