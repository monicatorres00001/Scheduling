#Solving Faculty-Course Allocation Problem Using Integer Programming Model

#FACULTY MEMBERS
set I; 
set I1;/*type 1 instructors*/
set I2; /*type 2 instructors*/
set P;
set P1; /*type 1 professors*/
set P2; /*type 2 professors*/

#CTIME BLOCKS
set tfirst;
set tfourth;
set wfirst;
set wfourth;
set thfirst;
set thfourth;
set ffirst;
set ffourth;

#SAME SCHEDULE
set MS1; /*same sched in monday subjects*/
set TS1; /*same sched in tuesday subjects*/
set TS2;
set TS3;
set TS4;
set TS5;
set TS6;
set TS7;
set TS8;
set TS9;
set TS10;
set TS11;
set TS12;
set TS13;
set TS14;
set WS1; /*same sched in wednesday subjects*/
set WS2;
set WS3;
set WS4;
set WS5;
set WS6;
set WS7;
set WS8;
set WS9;
set WS10;
set WS11;
set WS12;
set WS13;
set WS14;
set WS15;

set THS1; /*same sched in thursday subjects*/
set THS2;
set THS3;
set THS4;
set THS5;
set THS6;
set THS7;
set THS8;
set THS9;
set THS10;
set THS11;
set THS12;
set THS13;

set FS1; /*same sched in friday subjects*/
set FS2;
set FS3;
set FS4;
set FS5;
set FS6;
set FS7;
set FS8;
set FS9;
set FS10;
set FS11;
set FS12;
set FS13;
set FS14;

#SUBJECTS
set J;


#GE COURSES
set GE;

#GRADUATE courses
set GRA;


#UNDERGRAD SEMINAR
set US;

#3 UNIT LECTURE TYPE UG
set LEC;

#MAJOR COURSES
set MAJ;
set NMAJ;


#SP courses
set SP1;
set SPAmat;
set SPMath;
set SPMst;

#lab
set LAB;

#3U DIVIDED TO 2H LEC, 1H RECIT
set L3R;

#5U DIVIDED TO 3H LEC,2H RECIT
set L5R;

#LECTURE ASSISTANTS
set LA;

#1H RECIT CLASS (COMPLETE)
set REC;

#2H RECIT CLASS(COMPLETE)
set RECT;

/* fuzzy */
param v{p in P, j in J};
param w{i in I, j in J};

#rhs
param g; #18
param h; #0
param par; #6
param pa;#14
param oli{i in I};
param olp{p in P};
param OLI{i in I}:=oli[i];
param OLP{p in P}:=olp[p];
param a{i in I};#1
param b{p in P};#1
param c{p in P}:= g*b[p];#for GE COURSES
param w1{i in I}:=par*a[i];
param w2{i in I}:=pa*a[i];
param w3{p in P} :=par*b[p];
param w4{p in P} :=g*b[p];
param sub{j in J};
param ugc3{l3r in L3R};
param ugc5{l5r in L5R};
param gec{ge in GE};
param gradc{gra in GRA};
param undc{lec in LEC};
param spc{sp1 in SP1};
param q;

#instructors
var x{i in I, j in J},binary;

#professors
var y{p in P, j in J},binary;

maximize preferences: sum{p in P, j in J} v[p,j]*y[p,j]+ sum{i in I, j in J}w[i,j]*x[i,j];

	
/*faculty members cannot handle courses with same time slots*/
#MONDAY
	#instructors
	s.t. mondaysamei{i in I}: sum{ms1 in MS1} x[i,ms1] <=a[i];
	#professors
	s.t. mondaysamep{p in P}: sum{ms1 in MS1} y[p,ms1] <=b[p];

#TUESDAY

	#instructors
	s.t. tuesdaysamei1{i in I}: sum{ts1 in TS1} x[i,ts1] <=a[i];
	s.t. tuesdaysamei2{i in I}: sum{ts2 in TS2} x[i,ts2] <=a[i];
	s.t. tuesdaysamei3{i in I}: sum{ts3 in TS3} x[i,ts3] <=a[i];
	s.t. tuesdaysamei4{i in I}: sum{ts4 in TS4} x[i,ts4] <=a[i];
	s.t. tuesdaysamei5{i in I}: sum{ts5 in TS5} x[i,ts5] <=a[i];
	s.t. tuesdaysamei6{i in I}: sum{ts6 in TS6} x[i,ts6] <=a[i];
	s.t. tuesdaysamei7{i in I}: sum{ts7 in TS7} x[i,ts7] <=a[i];
	s.t. tuesdaysamei8{i in I}: sum{ts8 in TS8} x[i,ts8] <=a[i];
	s.t. tuesdaysamei9{i in I}: sum{ts9 in TS9} x[i,ts9] <=a[i];
	s.t. tuesdaysamei10{i in I}: sum{ts10 in TS10} x[i,ts10] <=a[i];
	s.t. tuesdaysamei11{i in I}: sum{ts11 in TS11} x[i,ts11] <=a[i];
	s.t. tuesdaysamei12{i in I}: sum{ts12 in TS12} x[i,ts12] <=a[i];
	s.t. tuesdaysamei13{i in I}: sum{ts13 in TS13} x[i,ts13] <=a[i];
	s.t. tuesdaysamei14{i in I}: sum{ts14 in TS14} x[i,ts14] <=a[i];
	#professsors
	s.t. tuesdaysamep1{p in P}: sum{ts1 in TS1} y[p,ts1] <=b[p];
	s.t. tuesdaysamep2{p in P}: sum{ts2 in TS2} y[p,ts2] <=b[p];
	s.t. tuesdaysamep3{p in P}: sum{ts3 in TS3} y[p,ts3] <=b[p];
	s.t. tuesdaysamep4{p in P}: sum{ts4 in TS4} y[p,ts4] <=b[p];
	s.t. tuesdaysamep5{p in P}: sum{ts5 in TS5} y[p,ts5] <=b[p];
	s.t. tuesdaysamep6{p in P}: sum{ts6 in TS6} y[p,ts6] <=b[p];
	s.t. tuesdaysamep7{p in P}: sum{ts7 in TS7} y[p,ts7] <=b[p];
	s.t. tuesdaysamep8{p in P}: sum{ts8 in TS8} y[p,ts8] <=b[p];
	s.t. tuesdaysamep9{p in P}: sum{ts9 in TS9} y[p,ts9] <=b[p];
	s.t. tuesdaysamep10{p in P}: sum{ts10 in TS10} y[p,ts10] <=b[p];
	s.t. tuesdaysamep11{p in P}: sum{ts11 in TS11} y[p,ts11] <=b[p];
	s.t. tuesdaysamep12{p in P}: sum{ts12 in TS12} y[p,ts12] <=b[p];
	s.t. tuesdaysamep13{p in P}: sum{ts13 in TS13} y[p,ts13] <=b[p];
	s.t. tuesdaysamep14{p in P}: sum{ts14 in TS14} y[p,ts14] <=b[p];

#WEDNESDAY
	#insructors
	s.t. wednesdaysamei1{i in I}: sum{ws1 in WS1} x[i,ws1] <=a[i];
	s.t. wednesdaysamei2{i in I}: sum{ws2 in WS2} x[i,ws2] <=a[i];
	s.t. wednesdaysamei3{i in I}: sum{ws3 in WS3} x[i,ws3] <=a[i];
	s.t. wednesdaysamei4{i in I}: sum{ws4 in WS4} x[i,ws4] <=a[i];
	s.t. wednesdaysamei5{i in I}: sum{ws5 in WS5} x[i,ws5] <=a[i];
	s.t. wednesdaysamei6{i in I}: sum{ws6 in WS6} x[i,ws6] <=a[i];
	s.t. wednesdaysamei7{i in I}: sum{ws7 in WS7} x[i,ws7] <=a[i];
	s.t. wednesdaysamei8{i in I}: sum{ws8 in WS8} x[i,ws8] <=a[i];
	s.t. wednesdaysamei9{i in I}: sum{ws9 in WS9} x[i,ws9] <=a[i];
	s.t. wednesdaysamei10{i in I}: sum{ws10 in WS10} x[i,ws10] <=a[i];
	s.t. wednesdaysamei11{i in I}: sum{ws11 in WS11} x[i,ws11] <=a[i];
	s.t. wednesdaysamei12{i in I}: sum{ws12 in WS12} x[i,ws12] <=a[i];
	s.t. wednesdaysamei13{i in I}: sum{ws13 in WS13} x[i,ws13] <=a[i];
	s.t. wednesdaysamei14{i in I}: sum{ws14 in WS14} x[i,ws14] <=a[i];
	s.t. wednesdaysamei15{i in I}: sum{ws15 in WS15} x[i,ws15] <=a[i];
	#professors
	s.t. wednesdaysamep1{p in P}: sum{ws1 in WS1} y[p,ws1] <=b[p];
	s.t. wednesdaysamep2{p in P}: sum{ws2 in WS2} y[p,ws2] <=b[p];
	s.t. wednesdaysamep3{p in P}: sum{ws3 in WS3} y[p,ws3] <=b[p];
	s.t. wednesdaysamep4{p in P}: sum{ws4 in WS4} y[p,ws4] <=b[p];
	s.t. wednesdaysamep5{p in P}: sum{ws5 in WS5} y[p,ws5] <=b[p];
	s.t. wednesdaysamep6{p in P}: sum{ws6 in WS6} y[p,ws6] <=b[p];
	s.t. wednesdaysamep7{p in P}: sum{ws7 in WS7} y[p,ws7] <=b[p];
	s.t. wednesdaysamep8{p in P}: sum{ws8 in WS8} y[p,ws8] <=b[p];
	s.t. wednesdaysamep9{p in P}: sum{ws9 in WS9} y[p,ws9] <=b[p];
	s.t. wednesdaysamep10{p in P}: sum{ws10 in WS10} y[p,ws10] <=b[p];
	s.t. wednesdaysamep11{p in P}: sum{ws11 in WS11} y[p,ws11] <=b[p];
	s.t. wednesdaysamep12{p in P}: sum{ws12 in WS12} y[p,ws12] <=b[p];
	s.t. wednesdaysamep13{p in P}: sum{ws13 in WS13} y[p,ws13] <=b[p];
	s.t. wednesdaysamep14{p in P}: sum{ws14 in WS14} y[p,ws14] <=b[p];
	s.t. wednesdaysamep15{p in P}: sum{ws15 in WS15} y[p,ws15] <=b[p];

#THURSDAY
	#instructors
	s.t. thursdaysamei1{i in I}: sum{ths1 in THS1} x[i,ths1] <=a[i];
	s.t. thursdaysamei2{i in I}: sum{ths2 in THS2} x[i,ths2] <=a[i];
	s.t. thursdaysamei3{i in I}: sum{ths3 in THS3} x[i,ths3] <=a[i];
	s.t. thursdaysamei4{i in I}: sum{ths4 in THS4} x[i,ths4] <=a[i];
	s.t. thursdaysamei5{i in I}: sum{ths5 in THS5} x[i,ths5] <=a[i];
	s.t. thursdaysamei6{i in I}: sum{ths6 in THS6} x[i,ths6] <=a[i];
	s.t. thursdaysamei7{i in I}: sum{ths7 in THS7} x[i,ths7] <=a[i];
	s.t. thursdaysamei8{i in I}: sum{ths8 in THS8} x[i,ths8] <=a[i];
	s.t. thursdaysamei9{i in I}: sum{ths9 in THS9} x[i,ths9] <=a[i];
	s.t. thursdaysamei10{i in I}: sum{ths10 in THS10} x[i,ths10] <=a[i];
	s.t. thursdaysamei11{i in I}: sum{ths11 in THS11} x[i,ths11] <=a[i];
	s.t. thursdaysamei12{i in I}: sum{ths12 in THS12} x[i,ths12] <=a[i];
	s.t. thursdaysamei13{i in I}: sum{ths13 in THS13} x[i,ths13] <=a[i];
	#professors
	s.t. thursdaysamep1{p in P}: sum{ths1 in THS1} y[p,ths1] <=b[p];
	s.t. thursdaysamep2{p in P}: sum{ths2 in THS2} y[p,ths2] <=b[p];
	s.t. thursdaysamep3{p in P}: sum{ths3 in THS3} y[p,ths3] <=b[p];
	s.t. thursdaysamep4{p in P}: sum{ths4 in THS4} y[p,ths4] <=b[p];
	s.t. thursdaysamep5{p in P}: sum{ths5 in THS5} y[p,ths5] <=b[p];
	s.t. thursdaysamep6{p in P}: sum{ths6 in THS6} y[p,ths6] <=b[p];
	s.t. thursdaysamep7{p in P}: sum{ths7 in THS7} y[p,ths7] <=b[p];
	s.t. thursdaysamep8{p in P}: sum{ths8 in THS8} y[p,ths8] <=b[p];
	s.t. thursdaysamep9{p in P}: sum{ths9 in THS9} y[p,ths9] <=b[p];
	s.t. thursdaysamep10{p in P}: sum{ths10 in THS10} y[p,ths10] <=b[p];
	s.t. thursdaysamep11{p in P}: sum{ths11 in THS11} y[p,ths11] <=b[p];
	s.t. thursdaysamep12{p in P}: sum{ths12 in THS12} y[p,ths12] <=b[p];
	s.t. thursdaysamep13{p in P}: sum{ths13 in THS13} y[p,ths13] <=b[p];

#FRIDAY
	#instructors
	s.t. fridaysamei1{i in I}: sum{fs1 in FS1} x[i,fs1] <=a[i];
	s.t. fridaysamei2{i in I}: sum{fs2 in FS2} x[i,fs2] <=a[i];
	s.t. fridaysamei3{i in I}: sum{fs3 in FS3} x[i,fs3] <=a[i];
	s.t. fridaysamei4{i in I}: sum{fs4 in FS4} x[i,fs4] <=a[i];
	s.t. fridaysamei5{i in I}: sum{fs5 in FS5} x[i,fs5] <=a[i];
	s.t. fridaysamei6{i in I}: sum{fs6 in FS6} x[i,fs6] <=a[i];
	s.t. fridaysamei7{i in I}: sum{fs7 in FS7} x[i,fs7] <=a[i];
	s.t. fridaysamei8{i in I}: sum{fs8 in FS8} x[i,fs8] <=a[i];
	s.t. fridaysamei9{i in I}: sum{fs9 in FS9} x[i,fs9] <=a[i];
	s.t. fridaysamei10{i in I}: sum{fs10 in FS10} x[i,fs10] <=a[i];
	s.t. fridaysamei11{i in I}: sum{fs11 in FS11} x[i,fs11] <=a[i];
	s.t. fridaysamei12{i in I}: sum{fs12 in FS12} x[i,fs12] <=a[i];
	s.t. fridaysamei13{i in I}: sum{fs13 in FS13} x[i,fs13] <=a[i];
	s.t. fridaysamei14{i in I}: sum{fs14 in FS14} x[i,fs14] <=a[i];
	#professors
	s.t. fridaysamep1{p in P}: sum{fs1 in FS1} y[p,fs1] <=b[p];
	s.t. fridaysamep2{p in P}: sum{fs2 in FS2} y[p,fs2] <=b[p];
	s.t. fridaysamep3{p in P}: sum{fs3 in FS3} y[p,fs3] <=b[p];
	s.t. fridaysamep4{p in P}: sum{fs4 in FS4} y[p,fs4] <=b[p];
	s.t. fridaysamep5{p in P}: sum{fs5 in FS5} y[p,fs5] <=b[p];
	s.t. fridaysamep6{p in P}: sum{fs6 in FS6} y[p,fs6] <=b[p];
	s.t. fridaysamep7{p in P}: sum{fs7 in FS7} y[p,fs7] <=b[p];
	s.t. fridaysamep8{p in P}: sum{fs8 in FS8} y[p,fs8] <=b[p];
	s.t. fridaysamep9{p in P}: sum{fs9 in FS9} y[p,fs9] <=b[p];
	s.t. fridaysamep10{p in P}: sum{fs10 in FS10} y[p,fs10] <=b[p];
	s.t. fridaysamep11{p in P}: sum{fs11 in FS11} y[p,fs11] <=b[p];
	s.t. fridaysamep12{p in P}: sum{fs12 in FS12} y[p,fs12] <=b[p];
	s.t. fridaysamep13{p in P}: sum{fs13 in FS13} y[p,fs13] <=b[p];
	s.t. fridaysamep14{p in P}: sum{fs14 in FS14} y[p,fs14] <=b[p];

#CLASSES CONSTRAINTS
/*total no of classes assigned=total no. of classes offered*/
	s.t. total1: sum{i in I,j in J} x[i,j] + sum{p in P, j in J} y[p,j]=259;

/*team teaching is not allowed*/ 
	s.t. tt1{j in J}: sum {i in I} x[i,j] + sum{p in P} y[p,j]=sub[j];

/*Limiting the subjects that can be taught by instructors */
s.t. l1{i in I,ge in GE}: x[i,ge]=0;
s.t. l2{i in I, gra in GRA}: x[i,gra]=0;
s.t. l3{i in I,us in US}: x[i,us]=0;
s.t. l4{i in I, maj in MAJ}: x[i,maj]=0;
s.t. l5{i in I, sp1 in SP1}: x[i,sp1]=0;

/*type 1 instructors*/
t3{i1 in I1, lec in LEC}: x[i1,lec]=0;
t4{i1 in I1, l3r in L3R}: x[i1,l3r]=0;
t5{i1 in I1, l5r in L5R}: x[i1,l5r]=0;

/*type 2 professors*/
	pt2{p2 in P2,la in LA}: y[p2,la]=0;

/*SP courses*/
	S1{p in P}:sum{spamat in SPAmat} y[p,spamat]<=b[p];
	S2{p in P}:sum{spmath in SPMath} y[p,spmath]<=b[p];
	S3{p in P}:sum{spmst in SPMst} y[p,spmst]<=b[p];

/*GE courses <=18*/
	G2{p in P}: 3*sum{ge in GE} y[p,ge]<=c[p];

/*Graduate Courses*/
	GR2{p in P}: 3*sum{gra in GRA} y[p,gra]<=c[p];


#WORKLOAD CONSTRAINTS
	wci1{i in I}:(sum{lec in LEC} undc[lec]*x[i,lec])+1.5*(sum{lab in LAB}x[i,lab])+(sum{l3r in L3R} ugc3[l3r]*x[i,l3r])+(sum{l5r in L5R} ugc5[l5r]*x[i,l5r]) + 0.5*(sum{la in LA} x[i,la])+ (sum{rec in REC} x[i,rec]) + 2*(sum{rect in RECT}x[i,rect])+OLI[i]>=w1[i];
	wci2{i in I}:(sum{lec in LEC} undc[lec]* x[i,lec])+1.5*(sum{lab in LAB}x[i,lab])+(sum{l3r in L3R} ugc3[l3r]*x[i,l3r])+(sum{l5r in L5R} ugc5[l5r]*x[i,l5r]) + 0.5*(sum{la in LA} x[i,la])+ (sum{rec in REC} x[i,rec]) + 2*(sum{rect in RECT}x[i,rect])+OLI[i]<=w2[i];
	wcp2{p in P}:(sum{ge in GE} gec[ge]*y[p,ge])+ (sum{gra in GRA} gradc[gra]* y[p,gra])+(sum{us in US} y[p,us])+ (sum{lec in LEC} undc[lec]* y[p,lec])+(sum{sp1 in SP1} spc[sp1]* y[p,sp1])+1.5*(sum{lab in LAB}y[p,lab])+(sum{l3r in L3R} ugc3[l3r]*y[p,l3r])+(sum{l5r in L5R} ugc5[l5r]*y[p,l5r]) + 0.5*(sum{la in LA} y[p,la])+ (sum{rec in REC} y[p,rec]) + 2*(sum{rect in RECT}y[p,rect])+OLP[p]>=w3[p];
	wcp3{p in P}:(3*sum{ge in GE} y[p,ge])+ (3*sum{gra in GRA} y[p,gra])+(sum{us in US} y[p,us])+ (3*sum{lec in LEC} y[p,lec])+(3*sum{sp1 in SP1} y[p,sp1])+(sum{lab in LAB}y[p,lab])+(2*sum{l3r in L3R} y[p,l3r])+(3*sum{l5r in L5R} y[p,l5r]) + (0.5*sum{la in LA} y[p,la])+ (sum{rec in REC} y[p,rec]) + (2*sum{rect in RECT} y[p,rect])<=w4[p];


s.t. cg3{i in I,tf in tfirst,tfo in tfourth}:x[i,tf]+x[i,tfo]<=1;

s.t. cg9{i in I,wf in wfirst,wfo in wfourth}:(x[i,wf]+x[i,wfo])<=1;

s.t. cg15{i in I,thf in thfirst,thfo in thfourth}:(x[i,thf]+x[i,thfo])<=1;

s.t. cg21{i in I,ff in ffirst,ffo in ffourth}:(x[i,ff]+x[i,ffo])<=1;

s.t. pcg3{p in P,tf in tfirst,tfo in tfourth}:(y[p,tf]+y[p,tfo])<=1;

s.t. pcg9{p in P,wf in wfirst,wfo in wfourth}:(y[p,wf]+y[p,wfo])<=1;

s.t. pcg15{p in P,thf in thfirst,thfo in thfourth}:(y[p,thf]+y[p,thfo])<=1;

s.t. pcg21{p in P,ff in ffirst,ffo in ffourth}:(y[p,ff]+y[p,ffo])<=1;

data;
#TIME BLOCKS
set tfirst:=B150B-1L W14S W17A-1R W17A-2R	W17A-3R W17A-4R W17A-5R W2S	W2SLA W26S W27A-2R W27A-3R W27A-4R	W27A-5R W191T W14B-1R	W14B-2R W14B-3R W14B-4R W14B-5R W17B-1R	W17B-2R W17B-3R W17B-4R W17B-5R W28T W38T;

set tfourth:=B170Y B178Y W155Y	W220Y W37G-1R W37G-2R	W37G-3R W11Y W37G-4R W17Y W37G-5R W37G-6R W174B-1L W11GH-1R	W11GH-2R W11GH-3R	W11GH-4R W11GH-5R	W14YZ B176Z	B19Z W1Z W1ZLA W111Z W17Z	W20Z	W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R;

set wfirst:=W14S-1R W14S-2R W14S-3R W14S-4R W14S-5R W17A	W26S-1R W26S-2R W26S-3R W26S-4R W26S-5R W27A	W17B	B150B	W14B	W174B W28T-1R W28T-2R	W28T-3R W28T-4R W28T-5R;

set wfourth:=W37G	W11Y-1R W11Y-2R W11Y-3R W11Y-4R W11Y-5R	W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R	W20G W11GH W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W151H W165H	W2H	W2HLA W36H W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R;

set thfirst:=B150B-2L W14S W17A-1R W17A-2R	W17A-3R W17A-4R W17A-5R W2S	W2SLA W26S W191T W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W28T W38T;

set thfourth:=W14YZ B170Y B178Y W155Y	W11Y	W17Y	W220Y W37G-1R W174B-5L	W37G-2R W37G-3R W37G-4R W37G-5R W37G-6R B176Z B19Z	W1Z	W1ZLA W111Z W17Z W20Z W36H-1R W36H-2R	W36H-3R W36H-4R W36H-5R;

set ffirst:=W17A	W27A	W17B	B150B	W14B	W174B W38T-3R W38T-4R W38T-5R;

set ffourth:=W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R	W20G	W37G W11GH W151H W165H W2H W2HLA W36H W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R	;

set I:=/*type1*/CHB FWM FEO GEB IJM KAB MSA QML RAE TDJ TJB VKB/*type2*/JSA CDN CBD ENA EJT HBS JEO LRR LIB LDM NAL RRB;

param a:=CHB 1 
FWM 1
FEO 1
GEB 1
IJM 1
KAB 1
MSA 1
QML 1
RAE 1
TDJ 1
TJB 1
VKB 1
JSA 1
CDN 1
CBD 1
ENA 1
EJT 1
HBS 1
JEO 1
LRR 1
LIB 1 
LDM 1
NAL 1
RRB 1;

#other loads
param oli:=CHB 0
FWM 3
FEO 0
GEB 3
IJM 0
KAB 3
MSA 3
QML 0
RAE 3
TDJ 3
TJB 0
VKB 3
JSA 3
CDN 3
CBD 3
ENA 4
EJT 3
HBS 3
JEO 3
LRR 0
LIB 3 
LDM 3
NAL 3
RRB 3;

param olp:=MGV 1
AMB 0
MVC 0
CGA 3
CAL 0
PRO 0
LMD 3
DCA 12
EIF 2
FDF 0
FLL 0
GMA 0
JEC 4.5
LVM 3
MJB 3
PJD 3
ULA 0
VBP 0
DLB 0
DAE 3
LJO 9
PRG 12
RRE 0
SVP 0;

set I1 :=CHB FWM FEO GEB IJM KAB MSA QML RAE TDJ TJB VKB;
set I2 :=JSA CDN CBD ENA EJT HBS JEO LRR LIB LDM NAL RRB;
set P := MGV AMB MVC CGA CAL PRO LMD DCA EIF FDF FLL GMA JEC LVM MJB PJD ULA VBP DLB DAE LJO PRG RRE SVP;
set P1 := /*type1*/MGV;
set P2 := AMB MVC CGA CAL PRO LMD DCA EIF FDF FLL GMA JEC LVM MJB PJD ULA VBP DLB DAE LJO PRG RRE SVP;
param b:=MGV 1
AMB 1
MVC 1
CGA 1
CAL 1
PRO 1
LMD 1
DCA 1
EIF 1
FDF 1
FLL 1
GMA 1
JEC 1
LVM 1
MJB 1
PJD 1
ULA 1
VBP 1
DLB 1
DAE 1
LJO 1
PRG 1
RRE 1
SVP 1;

param q:=1;
param g:=18;
param h:=0;
param par:=9;
param pa:=14;
param sub:= W2S 1 W1V 1 W1Z 1 W2D 1 W1F 1 W2H 1 W211U 1 W220Y 1 W230D 1 B199W1 1 B199W2 1 W191T 1 B112U 1 B167U 1 W143U 1 B174V 1 W155V 1 W181V 1 W195V 1 W141W 1 B19X 1 B191AX 1 W133X 1 W141X 1 B170Y 1 B178Y 1 B176Z 1 B19Z 1 W111Z 1 W20Z 1 W155Y 1  W18E 1 B160C 1 W151C 1 W120D 1 B172E 1 W181E 1 W20G 1 W151H 1 W165H 1 B190AR1 1 B190AR2 1 B190AR3 1 B190AR4 1 B190AR5 1 B190AR6 1 B190AR7 1 B190AR8 1 W190AR3 1 W190AR1 1 W190AR2 1 W190AR4 1 W190AR5 1 W190AR6 1  MST190AR10 1 MST190AR11 1 MST190AR12 1 MST190AR13 1 W101U-1L 1 W101U-2L 1 W101U-3L 1 W101U-4L 1 W101U-5L 1 W101U-6L 1 W101U-7L 1 W101U-8L 1 B150B-1L 1 W174B-1L 1 W174B-2L 1 W174B-3L 1 B150B-2L 1 W174B-4L 1 W174B-5L 1 B150B-3L 1 B150B-4L 1 W11Y 1 W11UV 1 W11V 1 W14S 1 W26S 1 W28T 1 W38T 1 W101U 1 W27W 1 W26W 1 W11WX 1 W14YZ 1 W27A 1 B150B 1 W14B 1 W174B 1 W11CD 1 W11D 1 W11E 1 W11GH 1 W26EF 1 W38F 1 W17U 1 W17X 1 W17Y 1 W37X 1 W17Z 1 W17A 1 W17B 1 W37C 1 W17E 1 W37G 1 W36H 1 W2SLA 1 W1VLA 1 W1ZLA 1 W101ULA 1 W2DLA 1 W1FLA 1 W2HLA 1 W27A-2R 1 W27A-3R 1 W27A-4R 1 W27A-5R 1 W14B-1R 1 W14B-2R 1 W14B-3R 1 W14B-4R 1 W14B-5R 1 W11CD-1R 1 W11CD-2R 1 W11CD-3R 1 W11CD-4R 1 W11CD-5R 1 W11D-1R 1 W11D-2R 1 W11D-3R 1 W11D-4R 1 W11D-5R 1 W11E-1R 1 W11E-2R 1 W11E-3R 1 W11E-4R 1 W11E-5R 1 W11GH-1R 1 W11GH-2R 1 W11GH-3R 1 W11GH-4R 1 W11GH-5R 1 W26EF-1R 1 W26EF-2R 1 W26EF-3R 1 W26EF-4R 1 W26EF-5R 1 W38F-5R 1 W11UV-1R 1 W11UV-2R 1 W11UV-3R 1 W11UV-4R 1 W11UV-5R 1 W11V-1R 1 W11V-2R 1 W11V-3R 1 W11V-4R 1 W11V-5R 1 W11WX-1R 1 W11WX-2R 1 W11WX-3R 1 W11WX-4R 1 W11WX-5R 1 W11Y-1R 1 W11Y-2R 1 W11Y-3R 1 W11Y-4R 1 W11Y-5R 1 W14S-1R 1 W14S-2R 1 W14S-3R 1 W14S-4R 1 W14S-5R 1 W14YZ-1R 1 W14YZ-2R 1 W14YZ-3R 1 W14YZ-4R 1 W14YZ-5R 1 W26S-1R 1 W26S-2R 1 W26S-3R 1 W26S-4R 1 W26S-5R 1 W26W-1R 1 W26W-2R 1 W26W-3R 1 W26W-4R 1 W26W-5R 1 W28T-1R 1 W28T-2R 1 W28T-3R 1 W28T-4R 1 W28T-5R 1 W38T-3R 1 W38T-4R 1 W38T-5R 1 W27W-1R 1 W27W-2R 1 W27W-3R 1 W27W-4R 1 W27W-5R 1 W17A-1R 1 W17A-2R 1 W17A-3R 1 W17A-4R 1 W17A-5R 1 W17B-1R 1 W17B-2R 1 W17B-3R 1 W17B-4R 1 W17B-5R 1 W17E-1R 1 W17E-2R 1 W17E-3R 1 W17E-4R 1 W17E-5R 1 W37C-1R 1 W37C-2R 1 W37C-3R 1 W37C-4R 1 W37C-5R 1 W37G-1R 1 W37G-2R 1 W37G-3R 1 W37G-4R 1 W37G-5R 1 W37G-6R 1 W36H-1R 1 W36H-2R 1 W36H-3R 1 W36H-4R 1 W36H-5R 1 W17U-1R 1 W17U-2R 1 W17U-3R 1 W17U-4R 1 W17U-5R 1 W17X-1R 1 W17X-2R 1 W17X-3R 1 W17X-4R 1 W17X-5R 1 W17Y-1R 1 W17Y-2R 1 W17Y-3R 1 W17Y-4R 1 W17Y-5R 1 W17Z-1R 1 W17Z-2R 1 W17Z-3R 1 W17Z-4R 1 W17Z-5R 1 W37X-1R 1 W37X-2R 1 W37X-3R 1 W37X-4R 1 W37X-5R 1;


set J := W2S W1V W1Z W2D W1F W2H W211U W220Y W230D B199W1 B199W2 W191T B112U B167U W143U B174V W155V W181V W195V W141W B19X B191AX W133X W141X B170Y B178Y B176Z B19Z W111Z W20Z W155Y W18E B160C W151C W120D B172E W181E W20G W151H W165H B190AR1 B190AR2 B190AR3 B190AR4 B190AR5 B190AR6 B190AR7 B190AR8 W190AR3 W190AR1 W190AR2 W190AR4 W190AR5 W190AR6 MST190AR10 MST190AR11 MST190AR12 MST190AR13 W101U-1L W101U-2L W101U-3L W101U-4L W101U-5L W101U-6L W101U-7L W101U-8L B150B-1L W174B-1L W174B-2L W174B-3L B150B-2L W174B-4L W174B-5L B150B-3L B150B-4L W11Y W11UV W11V W14S W26S W28T W38T W101U W27W W26W W11WX W14YZ W27A B150B W14B W174B W11CD W11D W11E W11GH W26EF W38F W17U W17X W17Y W37X W17Z W17A W17B W37C W17E W37G W36H W2SLA W1VLA W1ZLA W101ULA W2DLA W1FLA W2HLA W27A-2R W27A-3R W27A-4R W27A-5R W14B-1R W14B-2R W14B-3R W14B-4R W14B-5R W11CD-1R W11CD-2R W11CD-3R W11CD-4R W11CD-5R W11D-1R W11D-2R W11D-3R W11D-4R W11D-5R W11E-1R W11E-2R W11E-3R W11E-4R W11E-5R W11GH-1R W11GH-2R W11GH-3R W11GH-4R W11GH-5R W26EF-1R W26EF-2R W26EF-3R W26EF-4R W26EF-5R W38F-5R W11UV-1R W11UV-2R W11UV-3R W11UV-4R W11UV-5R W11V-1R W11V-2R W11V-3R W11V-4R W11V-5R W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R W11Y-1R W11Y-2R W11Y-3R W11Y-4R W11Y-5R W14S-1R W14S-2R W14S-3R W14S-4R W14S-5R W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W26S-1R W26S-2R W26S-3R W26S-4R W26S-5R W26W-1R W26W-2R W26W-3R W26W-4R W26W-5R W28T-1R W28T-2R W28T-3R W28T-4R W28T-5R W38T-3R W38T-4R W38T-5R W27W-1R W27W-2R W27W-3R W27W-4R W27W-5R W17A-1R W17A-2R W17A-3R W17A-4R W17A-5R W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W17E-1R W17E-2R W17E-3R W17E-4R W17E-5R W37C-1R W37C-2R W37C-3R W37C-4R W37C-5R W37G-1R W37G-2R W37G-3R W37G-4R W37G-5R W37G-6R W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R W17U-1R W17U-2R W17U-3R W17U-4R W17U-5R W17X-1R W17X-2R W17X-3R W17X-4R W17X-5R W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R W37X-1R W37X-2R W37X-3R W37X-4R W37X-5R;


#SAME SCHEDULE (MONDAY)
set MS1 := W101U-1L W101U-2L W101U-3L W101U-4L W101U-5L W101U-6L W101U-7L W101U-8L;

#SAME SCHEDULE (TUESDAY)
set TS1 := B150B-1L W14S W17A-1R W17A-2R W17A-3R W17A-4R W17A-5R W2S W2SLA W26S W27A-2R W27A-3R W27A-4R W27A-5R;
set TS2 := B150B-1L W14B-1R W14B-2R W14B-3R W14B-4R W14B-5R W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W191T W28T W38T;
set TS3 := B112U B167U W101U W101ULA W37C-1R W37C-2R W37C-3R W37C-4R W37C-5R W143U W17U W211U;
set TS4 := B112U B167U W11CD-1R W11CD-2R W11CD-3R W11CD-4R W11CD-5R W11UV W143U W17U W211U;
set TS5 := B174V W1V W1VLA W11CD-1R W11CD-2R W11CD-3R W11CD-4R W11CD-5R W11UV W155V W181V W195V;
set TS6 := B174V W1V W1VLA W11D-1R W11D-2R W11D-3R W11D-4R W11D-5R W11V W155V W181V W195V;
set TS7 := B199W1 W141W W27W W11E-1R W11E-2R W11E-3R W11E-4R W11E-5R W17E-1R W17E-2R W17E-3R W17E-4R W17E-5R W26W;
set TS8 := W141W W11WX W26EF-1R W26EF-2R W26EF-3R W26EF-4R W26EF-5R;
set TS9 := B19X B191AX W133X W141X W17X W37X W11WX W26EF-1R W26EF-2R W26EF-3R W26EF-4R W26EF-5R;
set TS10 := B19X B191AX W133X W141X W17X W37X W38F-5R;
set TS11 := B170Y B178Y W155Y W220Y W37G-1R W37G-2R W37G-3R W11Y W37G-4R W17Y W37G-5R W37G-6R W174B-1L;
set TS12:= B170Y B178Y W155Y W220Y W11GH-1R W11GH-2R W11GH-3R W11GH-4R W11GH-5R W17Y W14YZ W174B-1L;
set TS13 := B176Z B19Z W1Z W1ZLA W11GH-1R W11GH-2R W11GH-3R W11GH-4R W11GH-5R W111Z W14YZ W17Z W174B-1L W20Z;
set TS14 := B176Z B19Z W1Z W1ZLA W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R W111Z W17Z W174B-1L W20Z;

#SAME SCHEDULE (WEDNESDAY)
set WS1 := W14S-1R W14S-2R W14S-3R W14S-4R W14S-5R W17A W26S-1R W26S-2R W26S-3R W26S-4R W26S-5R W27A;
set WS2 := W17B B150B W14B W174B W28T-1R W28T-2R W28T-3R W28T-4R W28T-5R;
set WS3 := B160C W17U-1R W17U-2R W17U-3R W17U-4R W17U-5R W151C W174B-2L W37C;
set WS4 := B160C W11CD W11UV-1R W11UV-2R W11UV-3R W11UV-4R W11UV-5R W151C W174B-2L W37C;
set WS5 := W11CD W11UV-1R W11UV-2R W11UV-3R W11UV-4R W11UV-5R W120D W174B-2L W2D W2DLA W230D;
set WS6 := W11D W11V-1R W11V-2R W11V-3R W11V-4R W11V-5R W120D W174B-2L W2D W2DLA W230D;
set WS7 := B172E W11E W26W-1R W26W-2R W26W-3R W26W-4R W26W-5R W17E W174B-3L W18E W181E;
set WS8 := B172E W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R W17E W174B-3L W18E W181E W26EF;
set WS9 := W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R;
set WS10 := W1F W1FLA W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R W174B-3L W26EF;
set WS11 := W1F W1FLA W17X-1R W17X-2R W17X-3R W17X-4R W17X-5R W38F W174B-3L W37X-1R W37X-2R W37X-3R W37X-4R W37X-5R;
set WS12 := W37G W11Y-1R W11Y-2R W11Y-3R W11Y-4R W11Y-5R W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R W20G;
set WS13 := W37G W11GH W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W20G;
set WS14 := W151H W11GH W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W165H W2H W2HLA W36H;
set WS15 := W151H W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R W165H W2H W2HLA W36H;

#SAME SCHEDULE (THURSDAY)
set THS1 := B150B-2L W14S W17A-1R W17A-2R W17A-3R W17A-4R W17A-5R W2S W2SLA W26S;
set THS2 := B150B-2L W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W191T W28T W38T;
set THS3 := B112U B167U W101U W101ULA W143U W17U W211U W37C-1R W37C-2R W37C-3R W37C-4R W37C-5R;
set THS4 := B112U B167U W11UV W143U W17U W211U;
set THS5 := B174V W1V W1VLA W11UV W155V W181V W195V;
set THS6 := B174V W1V W1VLA W11V W155V W181V W195V;
set THS7 := B199W2 W141W W17E-1R W17E-2R W17E-3R W17E-4R W17E-5R W174B-4L W26W W27W;
set THS8 := W141W W11WX W174B-4L;
set THS9 := B19X B191AX W133X W11WX W141X W17X W37X W174B-4L;
set THS10 := B170Y B178Y W155Y W11Y W17Y W220Y W37G-1R W174B-5L W37G-2R W37G-3R W37G-4R W37G-5R W37G-6R;
set THS11 :=W14YZ B170Y B178Y W155Y W17Y W220Y W174B-5L;
set THS12 := W14YZ B176Z B19Z W1Z W1ZLA W111Z W17Z W20Z W174B-5L; 
set THS13:=B176Z B19Z W1Z W1ZLA W111Z W17Z W20Z W174B-5L W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R;

#SAME SCHEDULE (FRIDAY)
set FS1 := W17A W27A;
set FS2 := B150B W14B W17B W174B W38T-3R W38T-4R W38T-5R;
set FS3 := B150B-3L B160C W151C W17U-1R W17U-2R W17U-3R W17U-4R W17U-5R W37C;
set FS4 := B150B-3L B160C W11CD W151C W37C;
set FS5 := B150B-3L W11CD W120D W2D W2DLA W230D;
set FS6 := B150B-3L W11D W120D W2D W2DLA W230D;
set FS7 := B150B-4L B172E W11E W17E W18E W181E W27W-1R W27W-2R W27W-3R W27W-4R W27W-5R;
set FS8 := B150B-4L B172E W17E W18E W181E W26EF;
set FS9 := B150B-4L W1F W1FLA W26EF;
set FS10 := B150B-4L W1F W1FLA W17X-1R W17X-2R W17X-3R W17X-4R W17X-5R W37X-1R W37X-2R W37X-3R W37X-4R W37X-5R W38F;
set FS11 := W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R W20G W37G;
set FS12 := W11GH W20G W37G;
set FS13 := W11GH W151H W165H W2H W2HLA W36H;
set FS14 := W151H W165H W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R W2H W2HLA W36H;

#GE courses
set GE:= W2S W1V W1Z W2D W1F W2H;

#GRADUATE courses
set GRA:= W211U W220Y W230D;

#UNDERGRAD SEMINAR
set US:=B199W1 B199W2;

#3 UNIT LECTURE TYPE UG
set LEC:=W191T B112U B167U W143U B174V W155V W181V W195V W141W B19X B191AX W133X W141X B170Y B178Y B176Z B19Z W111Z W20Z W155Y W18E B160C W151C W120D B172E W181E W20G W151H W165H;

#MAJOR COURSES
set MAJ:= W191T B112U B167U W143U B174V W155V W181V W195V W141W B191AX W133X W141X B170Y B178Y B176Z W111Z W155Y B160C W151C W120D B172E W181E W151H W165H;


#SP courses
set SP1:=B190AR1 B190AR2 B190AR3 B190AR4 B190AR5 B190AR6 B190AR7 B190AR8 W190AR3 W190AR1 W190AR2 W190AR4 W190AR5 W190AR6 MST190AR10 MST190AR11 MST190AR12 MST190AR13;
	set SPAmat:=B190AR1 B190AR2 B190AR3 B190AR4 B190AR5 B190AR6 B190AR7 B190AR8;
	set SPMath:=W190AR3 W190AR1 W190AR2 W190AR4 W190AR5 W190AR6;
	set SPMst:=MST190AR10 MST190AR11 MST190AR12 MST190AR13;

#LAB courses
set LAB:= W101U-1L W101U-2L W101U-3L W101U-4L W101U-5L W101U-6L W101U-7L W101U-8L B150B-1L W174B-1L W174B-2L W174B-3L B150B-2L W174B-4L W174B-5L B150B-3L B150B-4L;

#3U DIVIDED TO 2H LEC, 1H RECIT
set L3R:= W11Y W11UV W11V W14S W26S W28T W38T W101U W27W W26W W11WX W14YZ W27A B150B W14B W174B W11CD W11D W11E W11GH W26EF W38F;

#5U DIVIDED TO 3H LEC,2H RECIT
set L5R:= W17U W17X W17Y W37X W17Z W17A W17B W37C W17E W37G W36H;

#LECTURE ASSISTANTS
set LA:= W2SLA W1VLA W1ZLA W101ULA W2DLA W1FLA W2HLA;


#1H RECIT CLASS (COMPLETE)
set REC:= W27A-2R W27A-3R W27A-4R W27A-5R W14B-1R W14B-2R W14B-3R W14B-4R W14B-5R W11CD-1R W11CD-2R W11CD-3R W11CD-4R W11CD-5R W11D-1R W11D-2R W11D-3R W11D-4R W11D-5R W11E-1R W11E-2R W11E-3R W11E-4R W11E-5R W11GH-1R W11GH-2R W11GH-3R W11GH-4R W11GH-5R W26EF-1R W26EF-2R W26EF-3R W26EF-4R W26EF-5R W38F-5R W11UV-1R W11UV-2R W11UV-3R W11UV-4R W11UV-5R W11V-1R W11V-2R W11V-3R W11V-4R W11V-5R W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R W11Y-1R W11Y-2R W11Y-3R W11Y-4R W11Y-5R W14S-1R W14S-2R W14S-3R W14S-4R W14S-5R W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W26S-1R W26S-2R W26S-3R W26S-4R W26S-5R W26W-1R W26W-2R W26W-3R W26W-4R W26W-5R W28T-1R W28T-2R W28T-3R W28T-4R W28T-5R W38T-3R W38T-4R W38T-5R W27W-1R W27W-2R W27W-3R W27W-4R W27W-5R;

#2H RECIT CLASS (COMPLETE)
set RECT:=W17A-1R W17A-2R W17A-3R W17A-4R W17A-5R W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W17E-1R W17E-2R W17E-3R W17E-4R W17E-5R W37C-1R W37C-2R W37C-3R W37C-4R W37C-5R W37G-1R W37G-2R W37G-3R W37G-4R W37G-5R W37G-6R W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R W17U-1R W17U-2R W17U-3R W17U-4R W17U-5R W17X-1R W17X-2R W17X-3R W17X-4R W17X-5R W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R W37X-1R W37X-2R W37X-3R W37X-4R W37X-5R;


param gec:=W2S 7.947 W1V 7.016 W1Z 6.85 W2D 7.98 W1F 7.98 W2H 7.98;
param gradc:= W211U 3 W220Y 3 W230D 3;
param undc:=W191T 3 B112U 3 B167U 3 W143U 3 B174V 3 W155V 3 W181V 3.15 W195V 3 W141W 3 B19X 3.275 B191AX 3 W133X 3 W141X 3 B170Y 3.35 B178Y 3 B176Z 3 B19Z 3 W111Z 3.125 W20Z 3.025 W155Y 3.075 W18E 3 B160C 3 W151C 3.15 W120D 3.175 B172E 3 W181E 3.025 W20G 3.25 W151H 3 W165H 3;
param spc:=B190AR1 1 B190AR2 3 B190AR3 1.5 B190AR4 2 B190AR5 2 B190AR6 3 B190AR7 1.5 B190AR8 0.5 W190AR3 1 W190AR1 2.5 W190AR2 2.5 W190AR4 1 W190AR5 2.5 W190AR6 0.5 MST190AR10 1 MST190AR11 1.5 MST190AR12 1 MST190AR13 1;

param ugc3:= W11Y 4 W11UV 4 W11V 4 W14S 2.95 W26S 3.967 W28T 4 W38T 2.55 W101U 3.817 W27W 3.533 W26W 4 W11WX 4 W14YZ 4 W27A 3.083 B150B 2.75 W14B 4 W174B 3.25 W11CD 4 W11D 4 W11E 4 W11GH 4 W26EF 3.85 W38F 2;
param ugc5 := W17U 5.625 W17X 5.65 W17Y 5.825 W37X 6 W17Z 6 W17A 6 W17B 5.6 W37C 6 W17E 6 W37G 6 W36H 6;

param v: W2S W1V W1Z W2D W1F W2H W211U W220Y W230D B199W1 B199W2 W191T B112U B167U W143U B174V W155V W181V W195V W141W B19X B191AX W133X W141X B170Y B178Y B176Z B19Z W111Z W20Z W155Y W18E B160C W151C W120D B172E W181E W20G W151H W165H B190AR1 B190AR2 B190AR3 B190AR4 B190AR5 B190AR6 B190AR7 B190AR8 W190AR3 W190AR1 W190AR2 W190AR4 W190AR5 W190AR6 MST190AR10 MST190AR11 MST190AR12 MST190AR13 W101U-1L W101U-2L W101U-3L W101U-4L W101U-5L W101U-6L W101U-7L W101U-8L B150B-1L W174B-1L W174B-2L W174B-3L B150B-2L W174B-4L W174B-5L B150B-3L B150B-4L W11Y W11UV W11V W14S W26S W28T W38T W101U W27W W26W W11WX W14YZ W27A B150B W14B W174B W11CD W11D W11E W11GH W26EF W38F W17U W17X W17Y W37X W17Z W17A W17B W37C W17E W37G W36H W2SLA W1VLA W1ZLA W101ULA W2DLA W1FLA W2HLA W27A-2R W27A-3R W27A-4R W27A-5R W14B-1R W14B-2R W14B-3R W14B-4R W14B-5R W11CD-1R W11CD-2R W11CD-3R W11CD-4R W11CD-5R W11D-1R W11D-2R W11D-3R W11D-4R W11D-5R W11E-1R W11E-2R W11E-3R W11E-4R W11E-5R W11GH-1R W11GH-2R W11GH-3R W11GH-4R W11GH-5R W26EF-1R W26EF-2R W26EF-3R W26EF-4R W26EF-5R W38F-5R W11UV-1R W11UV-2R W11UV-3R W11UV-4R W11UV-5R W11V-1R W11V-2R W11V-3R W11V-4R W11V-5R W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R W11Y-1R W11Y-2R W11Y-3R W11Y-4R W11Y-5R W14S-1R W14S-2R W14S-3R W14S-4R W14S-5R W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W26S-1R W26S-2R W26S-3R W26S-4R W26S-5R W26W-1R W26W-2R W26W-3R W26W-4R W26W-5R W28T-1R W28T-2R W28T-3R W28T-4R W28T-5R W38T-3R W38T-4R W38T-5R W27W-1R W27W-2R W27W-3R W27W-4R W27W-5R W17A-1R W17A-2R W17A-3R W17A-4R W17A-5R W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W17E-1R W17E-2R W17E-3R W17E-4R W17E-5R W37C-1R W37C-2R W37C-3R W37C-4R W37C-5R W37G-1R W37G-2R W37G-3R W37G-4R W37G-5R W37G-6R W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R W17U-1R W17U-2R W17U-3R W17U-4R W17U-5R W17X-1R W17X-2R W17X-3R W17X-4R W17X-5R W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R W37X-1R W37X-2R W37X-3R W37X-4R W37X-5R:=
MGV	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
AMB	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
MVC 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
CGA	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0.9	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
CAL	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
PRO	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
LMD	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
DCA	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0.9	0	0	0	0	0	0	0	0	0.1	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
EIF	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0.9	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
FDF	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0.9	0	0	0
FLL	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
GMA	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
JEC	0	0	0	0	0.9	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
LVM	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
MJB	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0.3	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
PJD	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
ULA	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.3	0.9	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0
VBP	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
DLB	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
DAE	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
LJO	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
PRG	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0.9	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
RRE	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
SVP	0	0.9	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0;

param w: W2S W1V W1Z W2D W1F W2H W211U W220Y W230D B199W1 B199W2 W191T B112U B167U W143U B174V W155V W181V W195V W141W B19X B191AX W133X W141X B170Y B178Y B176Z B19Z W111Z W20Z W155Y W18E B160C W151C W120D B172E W181E W20G W151H W165H B190AR1 B190AR2 B190AR3 B190AR4 B190AR5 B190AR6 B190AR7 B190AR8 W190AR3 W190AR1 W190AR2 W190AR4 W190AR5 W190AR6 MST190AR10 MST190AR11 MST190AR12 MST190AR13 W101U-1L W101U-2L W101U-3L W101U-4L W101U-5L W101U-6L W101U-7L W101U-8L B150B-1L W174B-1L W174B-2L W174B-3L B150B-2L W174B-4L W174B-5L B150B-3L B150B-4L W11Y W11UV W11V W14S W26S W28T W38T W101U W27W W26W W11WX W14YZ W27A B150B W14B W174B W11CD W11D W11E W11GH W26EF W38F W17U W17X W17Y W37X W17Z W17A W17B W37C W17E W37G W36H W2SLA W1VLA W1ZLA W101ULA W2DLA W1FLA W2HLA W27A-2R W27A-3R W27A-4R W27A-5R W14B-1R W14B-2R W14B-3R W14B-4R W14B-5R W11CD-1R W11CD-2R W11CD-3R W11CD-4R W11CD-5R W11D-1R W11D-2R W11D-3R W11D-4R W11D-5R W11E-1R W11E-2R W11E-3R W11E-4R W11E-5R W11GH-1R W11GH-2R W11GH-3R W11GH-4R W11GH-5R W26EF-1R W26EF-2R W26EF-3R W26EF-4R W26EF-5R W38F-5R W11UV-1R W11UV-2R W11UV-3R W11UV-4R W11UV-5R W11V-1R W11V-2R W11V-3R W11V-4R W11V-5R W11WX-1R W11WX-2R W11WX-3R W11WX-4R W11WX-5R W11Y-1R W11Y-2R W11Y-3R W11Y-4R W11Y-5R W14S-1R W14S-2R W14S-3R W14S-4R W14S-5R W14YZ-1R W14YZ-2R W14YZ-3R W14YZ-4R W14YZ-5R W26S-1R W26S-2R W26S-3R W26S-4R W26S-5R W26W-1R W26W-2R W26W-3R W26W-4R W26W-5R W28T-1R W28T-2R W28T-3R W28T-4R W28T-5R W38T-3R W38T-4R W38T-5R W27W-1R W27W-2R W27W-3R W27W-4R W27W-5R W17A-1R W17A-2R W17A-3R W17A-4R W17A-5R W17B-1R W17B-2R W17B-3R W17B-4R W17B-5R W17E-1R W17E-2R W17E-3R W17E-4R W17E-5R W37C-1R W37C-2R W37C-3R W37C-4R W37C-5R W37G-1R W37G-2R W37G-3R W37G-4R W37G-5R W37G-6R W36H-1R W36H-2R W36H-3R W36H-4R W36H-5R W17U-1R W17U-2R W17U-3R W17U-4R W17U-5R W17X-1R W17X-2R W17X-3R W17X-4R W17X-5R W17Y-1R W17Y-2R W17Y-3R W17Y-4R W17Y-5R W17Z-1R W17Z-2R W17Z-3R W17Z-4R W17Z-5R W37X-1R W37X-2R W37X-3R W37X-4R W37X-5R:=
CHB	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1
FWM 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
FEO 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
GEB 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
IJM	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
KAB 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
MSA 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
QML 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
RAE 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
TDJ 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
TJB 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1
VKB 	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1
JSA	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
CDN	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
CBD	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
ENA	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
EJT	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0.9	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
HBS	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
JEO	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1
LRR	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
LIB	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
LDM	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
NAL	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1
RRB	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.9	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.1	0.9;

end;
