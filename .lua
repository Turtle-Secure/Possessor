local v0=string.char;local v1=string.byte;local v2=string.sub;local v3=bit32 or bit ;local v4=v3.bxor;local v5=table.concat;local v6=table.insert;local function v7(v24,v25)local v26={};for v42=1, #v24 do v6(v26,v0(v4(v1(v2(v24,v42,v42 + 1 )),v1(v2(v25,1 + (v42% #v25) ,1 + (v42% #v25) + 1 )))%256 ));end return v5(v26);end local v8=tonumber;local v9=string.byte;local v10=string.char;local v11=string.sub;local v12=string.gsub;local v13=string.rep;local v14=table.concat;local v15=table.insert;local v16=math.ldexp;local v17=getfenv or function()return _ENV;end ;local v18=setmetatable;local v19=pcall;local v20=select;local v21=unpack or table.unpack ;local v22=tonumber;local function v23(v27,v28,...)local v29=0;local v30;local v31;local v32;local v33;local v34;local v35;local v36;local v37;local v38;local v39;local v40;local v41;while true do if (v29==0) then v30=2 -1 ;v31=nil;v27=v12(v11(v27,5),v7("\87\165","\219\121\139\65\108\191"),function(v43)if (v9(v43,2)==79) then local v89=0;while true do if (v89==0) then v31=v8(v11(v43,1 + 0 ,2 -1 ));return "";end end else local v90=v10(v8(v43,16));if v31 then local v97=0;local v98;while true do if (v97==1) then return v98;end if (v97==0) then v98=v13(v90,v31);v31=nil;v97=1;end end else return v90;end end end);v29=1;end if (v29==5) then v38=v35;v39=nil;function v39(...)return {...},v20("#",...);end v29=6;end if (v29==1) then v32=nil;function v32(v44,v45,v46)if v46 then local v91=0;local v92;while true do if (v91==0) then v92=(v44/(2^(v45-1)))%((3 -1)^(((v46-1) -(v45-1)) + 1)) ;return v92-(v92%1) ;end end else local v93=2^(v45-(2 -1)) ;return (((v44%(v93 + v93))>=v93) and 1) or 0 ;end end v33=nil;v29=2;end if (v29==6) then v40=nil;function v40()local v47={};local v48={};local v49={};local v50={v47,v48,nil,v49};local v51=v35();local v52={};for v80=1,v51 do local v81=v33();local v82;if (v81==1) then v82=v33()~=0 ;elseif (v81==2) then v82=v36();elseif (v81==3) then v82=v37();end v52[v80]=v82;end v50[3]=v33();for v84=2 -1 ,v35() do local v85=0;local v86;while true do if (v85==0) then v86=v33();if (v32(v86,1,1)==0) then local v118=0;local v119;local v120;local v121;while true do if (v118==1) then v121={v34(),v34(),nil,nil};if (v119==0) then local v129=0;while true do if (v129==0) then v121[3]=v34();v121[8 -4 ]=v34();break;end end elseif (v119==(878 -(282 + 595))) then v121[3]=v35();elseif (v119==2) then v121[3]=v35() -((1639 -(1523 + 114))^(15 + 1)) ;elseif (v119==3) then local v140=0;while true do if (v140==0) then v121[3]=v35() -(2^16) ;v121[4]=v34();break;end end end v118=2;end if (0==v118) then v119=v32(v86,2,3);v120=v32(v86,4,6);v118=1;end if (v118==3) then if (v32(v120,3,3)==1) then v121[4]=v52[v121[4]];end v47[v84]=v121;break;end if (v118==2) then if (v32(v120,1 -0 ,1)==1) then v121[2 + 0 ]=v52[v121[2]];end if (v32(v120,793 -(368 + 423) ,2)==1) then v121[3 -0 ]=v52[v121[3]];end v118=3;end end end break;end end end for v87=1,v35() do v48[v87-(1066 -(68 + 997)) ]=v40();end return v50;end v41=nil;v29=7;end if (v29==3) then v35=nil;function v35()local v54,v55,v56,v57=v9(v27,v30,v30 + 3 );v30=v30 + 4 ;return (v57 * (22064430 -5287214)) + (v56 * (168813 -103277)) + (v55 * 256) + v54 ;end v36=nil;v29=4;end if (v29==7) then function v41(v58,v59,v60)local v61=0;local v62;local v63;local v64;while true do if (1==v61) then v64=v58[3];return function(...)local v99=v62;local v100=v63;local v101=v64;local v102=v39;local v103=1;local v104= -1;local v105={};local v106={...};local v107=v20("#",...) -(1271 -(226 + 1044)) ;local v108={};local v109={};for v115=0,v107 do if (v115>=v101) then v105[v115-v101 ]=v106[v115 + 1 ];else v109[v115]=v106[v115 + 1 ];end end local v110=(v107-v101) + 1 ;local v111;local v112;while true do local v116=0;while true do if (v116==1) then if (v112<=21) then if (v112<=(43 -33)) then if (v112<=(22 -(10 + 8))) then if (v112<=1) then if (v112>(117 -(32 + 85))) then if v109[v111[2 + 0 ]] then v103=v103 + 1 ;else v103=v111[3];end else v103=v111[3];end elseif (v112<=2) then local v142=0;local v143;while true do if (v142==0) then v143=v111[1 + 1 ];v109[v143]=v109[v143](v21(v109,v143 + 1 ,v111[3]));break;end end elseif (v112==(960 -(892 + 65))) then do return v109[v111[4 -2 ]]();end elseif (v109[v111[2]]==v111[15 -11 ]) then v103=v103 + 1 ;else v103=v111[3];end elseif (v112<=(449 -(416 + 26))) then if (v112<=5) then v109[v111[2]]();elseif (v112>6) then local v183=0;local v184;local v185;while true do if (v183==0) then v184=v111[3 -1 ];v185=v109[v111[4 -1 ]];v183=1;end if (v183==1) then v109[v184 + 1 ]=v185;v109[v184]=v185[v111[4]];break;end end else local v186=v111[2];local v187=v109[v186];for v230=v186 + 1 ,v104 do v15(v187,v109[v230]);end end elseif (v112<=8) then local v144=0;local v145;while true do if (v144==0) then v145=v111[352 -(87 + 263) ];do return v21(v109,v145,v104);end break;end end elseif (v112==9) then local v188=0;local v189;local v190;local v191;local v192;while true do if (1==v188) then v104=(v191 + v189) -1 ;v192=0;v188=2;end if (v188==2) then for v267=v189,v104 do local v268=0;while true do if (v268==0) then v192=v192 + 1 ;v109[v267]=v190[v192];break;end end end break;end if (v188==0) then v189=v111[2];v190,v191=v102(v109[v189](v21(v109,v189 + 1 ,v111[3])));v188=1;end end else local v193=v111[2];do return v21(v109,v193,v104);end end elseif (v112<=15) then if (v112<=12) then if (v112>(35 -24)) then v109[v111[2]]=v111[3];else do return;end end elseif (v112<=13) then v109[v111[2]]=v41(v100[v111[3]],nil,v60);elseif (v112==(194 -(67 + 113))) then v109[v111[2]]={};elseif (v109[v111[2]]==v111[4]) then v103=v103 + 1 ;else v103=v111[3];end elseif (v112<=18) then if (v112<=16) then if ((v111[3]==v7("\111\96\82\21","\211\48\37\28\67\90\191")) or (v111[3]==v7("\27\76\3\126\130\250\10","\148\124\41\119\24\231"))) then v109[v111[2]]=v60;else v109[v111[1 + 1 ]]=v60[v111[3]];end elseif (v112==(13 + 4)) then v109[v111[3 -1 ]]=v41(v100[v111[3]],nil,v60);else v109[v111[2]]=v109[v111[3]][v111[4]];end elseif (v112<=19) then v109[v111[2]]=v59[v111[3]];elseif (v112>20) then v109[v111[2]]=v59[v111[3]];else do return;end end elseif (v112<=(470 -(145 + 293))) then if (v112<=26) then if (v112<=23) then if (v112>22) then v109[v111[432 -(44 + 386) ]]=v109[v111[1489 -(998 + 488) ]][v111[4]];else do return v109[v111[2]]();end end elseif (v112<=24) then if ((v111[3]==v7("\46\167\3\147","\183\113\226\77\197")) or (v111[3]==v7("\71\92\161\218\69\87\163","\188\32\57\213"))) then v109[v111[2]]=v60;else v109[v111[2]]=v60[v111[3]];end elseif (v112>(61 -36)) then local v206=0;local v207;while true do if (v206==0) then v207=v111[2];v109[v207]=v109[v207](v21(v109,v207 + 1 ,v104));break;end end else local v208=0;local v209;while true do if (v208==0) then v209=v111[2];do return v109[v209](v21(v109,v209 + 1 ,v111[3]));end break;end end end elseif (v112<=29) then if (v112<=27) then v109[v111[2]]=v111[1 + 2 ];elseif (v112>28) then local v210=0;local v211;local v212;local v213;while true do if (v210==2) then for v269=1,v111[4] do v103=v103 + 1 ;local v270=v99[v103];if (v270[1]==(28 + 10)) then v213[v269-1 ]={v109,v270[775 -(201 + 571) ]};else v213[v269-1 ]={v59,v270[3]};end v108[ #v108 + 1 ]=v213;end v109[v111[2]]=v41(v211,v212,v60);break;end if (v210==0) then v211=v100[v111[3]];v212=nil;v210=1;end if (v210==1) then v213={};v212=v18({},{[v7("\203\63\68\85\18\241\24","\118\148\96\45\59")]=function(v272,v273)local v274=0;local v275;while true do if (0==v274) then v275=v213[v273];return v275[1][v275[2]];end end end,[v7("\105\141\254\21\163\95\188\244\21\172","\212\54\210\144\112")]=function(v276,v277,v278)local v279=v213[v277];v279[1][v279[2]]=v278;end});v210=2;end end else for v232=v111[2],v111[3] do v109[v232]=nil;end end elseif (v112<=30) then local v155=0;local v156;while true do if (v155==0) then v156=v111[2];do return v109[v156](v21(v109,v156 + 1 ,v111[3]));end break;end end elseif (v112>31) then local v214=0;local v215;while true do if (0==v214) then v215=v111[2];v109[v215]=v109[v215](v21(v109,v215 + 1 ,v111[1141 -(116 + 1022) ]));break;end end else v109[v111[2]]={};end elseif (v112<=37) then if (v112<=34) then if (v112==33) then if v109[v111[2]] then v103=v103 + 1 ;else v103=v111[12 -9 ];end else local v157=0;local v158;local v159;while true do if (v157==0) then v158=v111[2];v159=v109[v158];v157=1;end if (v157==1) then for v243=v158 + (3 -2) ,v104 do v15(v159,v109[v243]);end break;end end end elseif (v112<=35) then v109[v111[2]]=v109[v111[3]];elseif (v112==36) then v109[v111[2]]();else local v218=v111[2];local v219,v220=v102(v109[v218](v21(v109,v218 + 1 ,v111[3])));v104=(v220 + v218) -1 ;local v221=0;for v237=v218,v104 do local v238=0;while true do if (v238==0) then v221=v221 + 1 ;v109[v237]=v219[v221];break;end end end end elseif (v112<=40) then if (v112<=38) then v109[v111[2]]=v109[v111[3]];elseif (v112==(23 + 16)) then local v222=v111[954 -(802 + 150) ];v109[v222]=v109[v222](v21(v109,v222 + 1 ,v104));else for v239=v111[2],v111[7 -4 ] do v109[v239]=nil;end end elseif (v112<=41) then local v164=v100[v111[10 -7 ]];local v165;local v166={};v165=v18({},{[v7("\180\185\39\141\143\131\54","\227\235\230\78")]=function(v168,v169)local v170=0;local v171;while true do if (v170==0) then v171=v166[v169];return v171[1][v171[2]];end end end,[v7("\100\140\38\10\235\217\71\27\94\171","\127\59\211\72\111\156\176\41")]=function(v172,v173,v174)local v175=0;local v176;while true do if (v175==0) then v176=v166[v173];v176[1][v176[2]]=v174;break;end end end});for v177=1,v111[14 -10 ] do local v178=0;local v179;while true do if (v178==1) then if (v179[1]==38) then v166[v177-1 ]={v109,v179[3]};else v166[v177-1 ]={v59,v179[3]};end v108[ #v108 + 1 ]=v166;break;end if (v178==0) then v103=v103 + (1 -0) ;v179=v99[v103];v178=1;end end end v109[v111[2]]=v41(v164,v165,v60);elseif (v112>42) then local v224=0;local v225;local v226;while true do if (v224==1) then v109[v225 + 1 ]=v226;v109[v225]=v226[v111[4]];break;end if (v224==0) then v225=v111[2];v226=v109[v111[3]];v224=1;end end else v103=v111[3];end v103=v103 + (860 -(814 + 45)) ;break;end if (v116==0) then v111=v99[v103];v112=v111[1];v116=1;end end end end;end if (0==v61) then v62=v58[3 -2 ];v63=v58[2];v61=1;end end end return v41(v40(),{},v28)(...);end if (4==v29) then function v36()local v65=v35();local v66=v35();local v67=1;local v68=(v32(v66,1,20) * ((621 -(555 + 64))^32)) + v65 ;local v69=v32(v66,21,31);local v70=((v32(v66,32)==1) and  -1) or 1 ;if (v69==(931 -(857 + 74))) then if (v68==0) then return v70 * 0 ;else v69=1;v67=0;end elseif (v69==2047) then return ((v68==(568 -(367 + 201))) and (v70 * (1/0))) or (v70 * NaN) ;end return v16(v70,v69-(1950 -(214 + 713)) ) * (v67 + (v68/(2^52))) ;end v37=nil;function v37(v71)local v72=0;local v73;local v74;while true do if (v72==2) then v74={};for v113=1188 -(1069 + 118) , #v73 do v74[v113]=v10(v9(v11(v73,v113,v113)));end v72=3;end if (v72==0) then v73=nil;if  not v71 then local v117=0;while true do if (v117==0) then v71=v35();if (v71==0) then return "";end break;end end end v72=1;end if (v72==1) then v73=v11(v27,v30,(v30 + v71) -1 );v30=v30 + v71 ;v72=2;end if (3==v72) then return v14(v74);end end end v29=5;end if (v29==2) then function v33()local v75=0;local v76;while true do if (v75==0) then v76=v9(v27,v30,v30);v30=v30 + 1 ;v75=1;end if (v75==1) then return v76;end end end v34=nil;function v34()local v77=0;local v78;local v79;while true do if (v77==0) then v78,v79=v9(v27,v30,v30 + 2 );v30=v30 + 2 + 0 ;v77=1;end if (1==v77) then return (v79 * 256) + v78 ;end end end v29=3;end end end v23(v7("\171\204\106\1\30\211\176\105\16\30\215\176\22\22\29\168\179\22\23\29\208\183\17\18\24\222\181\99\22\25\215\176\22\21\29\168\179\22\22\106\209\178\17\20\24\212\181\30\16\29\215\187\21\111\30\215\180\18\22\104\209\198\17\21\24\163\181\20\22\27\208\177\22\19\30\210\176\105\16\30\208\179\16\19\24\214\177\105\22\109\215\179\22\100\29\168\179\22\17\28\214\179\21\111\30\215\179\23\19\97\215\179\20\16\31\213\182\105\16\30\215\177\22\16\31\213\178\22\16\30\215\178\22\16\30\212\176\105\16\30\214\177\23\16\30\215\179\20\16\30\215\183\21\111\30\215\179\16\17\106\215\179\22\19\29\168\179\22\16\31\215\179\22\20\28\168\179\22\18\24\212\204\22\16\30\214\183\105\16\30\213\181\30\111\30\215\177\16\19\97\215\179\22\18\26\168\179\22\18\24\212\204\22\16\30\212\183\105\16\30\213\176\22\16\30\211\179\22\16\29\211\204\22\16\30\212\179\22\16\26\215\179\22\17\26\168\179\22\16\111\215\179\22\20\24\168\179\22\16\108\212\204\22\16\30\214\176\105\16\30\215\178\21\111\30\215\179\18\19\97\215\179\22\18\25\168\179\22\20\30\215\176\22\21\29\168\179\22\19\111\213\182\16\20\28\165\176\103\18\97\215\176\21\111\30\215\177\19\22\26\213\193\22\18\24\168\179\22\102\30\212\197\22\16\31\165\176\105\16\30\215\177\23\17\22\168\179\22\17\29\215\179\22\17\24\168\179\22\17\29\215\179\22\18\30\215\179\23\20\97\215\179\23\19\30\215\179\21\16\30\215\178\18\111\30\215\179\99\16\30\215\183\16\111\30\215\178\21\16\30\215\182\22\16\30\213\183\105\16\30\213\176\22\16\30\209\181\105\16\30\214\192\22\16\30\208\179\22\16\25\211\204\22\16\28\210\179\22\16\27\215\179\22\23\26\168\179\22\16\24\215\179\22\20\29\168\179\22\16\31\215\179\20\16\31\213\179\22\16\26\215\179\22\20\30\215\179\23\16\30\214\177\22\99\30\215\179\19\16\30\215\177\18\111\30\215\177\22\16\30\215\176\22\16\30\210\179\22\16\28\215\179\23\18\30\164\179\22\16\26\215\179\22\19\26\168\179\22\18\27\215\179\22\18\30\215\179\18\20\97\215\179\20\23\30\215\179\23\19\97\215\179\22\18\30\215\177\16\16\26\215\179\22\17\30\215\178\17\16\30\215\178\22\16\30\211\179\22\16\26\213\194\21\111\30\215\178\17\16\30\215\178\20\111\30\215\177\21\16\30\215\178\16\111\30\215\179\99\16\30\215\177\16\111\30\215\178\99\16\30\215\178\22\16\30\213\183\105\16\30\215\194\22\16\30\214\182\105\16\30\215\183\20\97\29\168\179\22\17\111\215\179\22\17\28\168\179\22\17\29\215\179\22\17\30\215\179\21\20\97\215\179\22\19\30\215\179\23\16\30\215\178\18\111\30\215\179\103\16\30\215\178\16\111\30\215\179\100\19\97\215\179\22\17\29\168\179\22\16\31\212\204\22\16\30\210\176\105\16\30\215\176\22\97\29\168\179\22\22\109\209\197\16\17\24\211\180\21\23\26\208\177\16\25\24\162\181\17\16\29\215\183\21\111\30\215\181\17\22\31\209\199\16\21\30\212\179\17\19\97\215\179\18\24\28\168\180\18\23\30\211\180\16\21\25\211\179\21\20\28\212\204\22\16\24\223\177\105\23\26\208\179\17\19\29\166\177\105\18\104\208\177\16\17\25\208\177\99\22\25\209\186\17\20\24\223\180\19\22\28\208\182\17\19\24\210\180\20\22\29\209\197\16\101\25\211\181\19\22\107\208\183\20\101\24\212\181\96\22\106\213\197\19\19\24\222\181\18\22\22\208\176\16\98\25\212\181\103\23\29\209\194\17\19\24\223\177\96\21\30\209\197\20\111\25\212\181\19\18\97\208\176\16\102\25\213\177\96\22\106\209\178\16\25\24\162\177\96\18\107\209\192\17\21\24\214\179\20\22\97\215\179\96\16\29\161\179\23\16\109\212\204\22\16\30\209\177\23\19\97\215\179\22\97\30\215\179\23\19\97\215\179\22\20\28\166\176\105\16\30\215\194\22\16\30\214\179\22\17\28\214\179\22\16\30\214\179\22\16\31\212\204\22\16\31\213\178\22\16\30\215\177\22\16\30\213\176\105\16\30\213\179\22\23\30\215\179\20\16\30\215\177\22\16\30\212\179\22\17\28\215\192\22\16\30\211\179\22\16\26\211\204\22\16\28\210\179\22\16\28\215\179\22\20\26\168\179\22\18\25\215\179\22\17\29\168\179\22\16\28\213\204\22\16\28\211\179\22\16\31\215\179\22\17\30\215\179\23\16\30\215\183\20\97\29\168\179\22\16\108\215\179\22\17\30\215\177\22\17\28\215\179\22\17\29\168\179\22\16\27\213\204\22\16\30\165\176\105\16\30\215\178\17\111\30\215","\46\231\131\38\32"),v17(),...);
