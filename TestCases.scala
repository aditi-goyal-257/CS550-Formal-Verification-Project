import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import stainless.lang.StaticChecks._

import scala.annotation.tailrec
import java.io._

import point2d.*
import helper.*
import listLemmas.*
import sparsity.*
import sparsityLemmas.*
import bruteForce.*
import lemmas.*
import ClosestPoint.*
import Generator.*



object Testing:
    extension (pt: Point) {
        def printPoint (): String = {
            s"Point(${pt.x},${pt.y})"
        }
    }

    def prettyDisplay(p: PairPoint): String = {
        s"${p._1.printPoint()}, ${p._2.printPoint()}"
    }

    @tailrec
    def generateSomePoints(n: Int, acc: List[Point] = List[Point]() ): List[Point] = {

        if(n == 0) then acc else generateSomePoints(n-1 , pointGenerator.generate() :: acc )

    }
       
    @extern def main(args: Array[String]): Unit = {

        /* Self made test cases */
        // println(prettyDisplay(findClosestPair(List(Point(1,2), Point(3,4)))))
        // println(prettyDisplay(findClosestPair(List(Point(2, 3), Point(12, 30), Point(40,50), Point(5, 1), Point(12, 10), Point(3, 4)))))
        // println(prettyDisplay(findClosestPair(List(Point(0, 0), Point(-2, 0), Point(4, 0), Point(1, 1), Point(3, 3), Point(-2, 2), Point(5, 2)))))

       /* Test cases taken from https://github.com/Tosha1409/Closest_pair_of_points/blob/master/testcases.py */
        // val points1 = List(Point(637, -932), Point(-993, 176), Point(693, 817), Point(418, -676), Point(-266, -531), Point(-179, -874), Point(-926, -332), Point(-379, 757), Point(-8, 183), Point(-991, 262), Point(880, 978), Point(-346, 528), Point(-258, -852), Point(-41, -124), Point(806, 901), Point(-189, -707), Point(393, -95), Point(905, -461), Point(127, -367), Point(-236, -204), Point(-527, 538), Point(-519, 552), Point(259, 330), Point(506, -730), Point(818, 821), Point(337, 283), Point(856, -879), Point(-511, 907), Point(-450, -145), Point(960, -344), Point(237, 338), Point(-38, -236), Point(-142, -238), Point(-95, 941), Point(-920, 764), Point(-464, 506), Point(-506, 636), Point(-153, 318), Point(-537, 826), Point(322, -616), Point(134, 561), Point(-13, 49), Point(-633, 179), Point(273, 289), Point(559, -67), Point(825, -477), Point(220, 830), Point(595, 736), Point(-329, 783), Point(447, 428), Point(451, 473), Point(929, 4), Point(281, -1000), Point(-695, 714), Point(-272, 15), Point(353, -92), Point(718, 3), Point(-697, -320), Point(-308, 304), Point(-46, -21), Point(464, -456), Point(395, -240), Point(-563, 569), Point(-126, 483), Point(150, -397), Point(-277, -522), Point(955, 960), Point(906, -576), Point(-960, 710), Point(37, -12), Point(-785, -988), Point(875, 311), Point(-538, -288), Point(-21, -836), Point(-961, -88), Point(-355, -211), Point(171, 835), Point(859, -420), Point(-300, -252), Point(178, -751), Point(385, 254), Point(-808, -114), Point(-895, -453), Point(-574, 167), Point(330, -750), Point(-496, -386), Point(-17, -416), Point(-756, -195), Point(832, 36), Point(-566, 123), Point(294, -449), Point(-366, 754), Point(431, 565), Point(9, -29), Point(-398, -214), Point(248, -236), Point(669, -700), Point(-794, -181), Point(-391, -855), Point(-45, -775), Point(391, -176), Point(694, -205), Point(569, 704), Point(-348, -110), Point(-669, 343), Point(933, -642), Point(226, 393), Point(223, -667), Point(763, 727), Point(739, -901), Point(-390, 771), Point(660, 393), Point(620, -71), Point(167, -624), Point(-325, 697), Point(584, 90), Point(-751, -574), Point(-73, -569), Point(938, -647), Point(-179, 598), Point(-681, 566), Point(-511, 520), Point(-258, -331), Point(13, 930), Point(656, -995), Point(907, -377), Point(634, -691), Point(89, -982), Point(-408, -816), Point(-544, 168), Point(804, -599), Point(-544, -401), Point(108, -30), Point(217, -166), Point(298, 405), Point(-773, -102), Point(-853, -370), Point(15, 629), Point(83, 944), Point(441, -484), Point(232, 381), Point(901, 80), Point(-819, -657), Point(-886, -665), Point(-691, 61), Point(-140, -271), Point(106, 20), Point(-156, 119), Point(726, -148), Point(-922, 448))
        // val points2 = List(Point(649, -188), Point(-452, -588), Point(-595, 268), Point(-906, -114), Point(-815, -1), Point(832, -847), Point(-817, -945), Point(-993, 402), Point(956, 951), Point(106, 681), Point(-258, 478), Point(147, 855), Point(145, -887), Point(121, -130), Point(-56, -330), Point(721, 676), Point(774, -182), Point(310, 552), Point(845, -414), Point(497, 521), Point(191, -441), Point(-440, -403), Point(-558, 736), Point(151, -375), Point(202, -775), Point(587, 328), Point(-519, 526), Point(-898, -980), Point(955, 185), Point(596, -445), Point(649, 432), Point(-495, 492), Point(-728, 423), Point(-868, -772), Point(280, 443), Point(-24, -351), Point(998, 981), Point(-320, -512), Point(772, 566), Point(846, -220), Point(-152, 488), Point(216, -294), Point(401, 830), Point(378, 971), Point(-853, -971), Point(186, -353), Point(-768, -47), Point(-672, 986), Point(-9, 72), Point(-542, -444), Point(-121, 874), Point(-473, -319), Point(664, -240), Point(293, -18), Point(-999, -747), Point(594, -164), Point(335, 128), Point(185, -438), Point(768, -974), Point(471, -599), Point(986, 504), Point(-534, -491), Point(-315, 814), Point(961, 569), Point(319, -529), Point(-516, -894), Point(-281, -875), Point(-985, -61), Point(670, 776), Point(765, 965), Point(82, -97), Point(948, 79), Point(-546, -849), Point(770, 192), Point(-565, -58), Point(-612, -968), Point(44, 947), Point(-466, 813), Point(424, -570), Point(640, 618), Point(-445, 93), Point(-930, 932), Point(760, -85), Point(-212, 963), Point(637, 772), Point(-686, 13), Point(556, -287), Point(-160, -149), Point(563, 959), Point(765, -470), Point(706, -458), Point(786, -93), Point(806, 268), Point(-46, -424), Point(-916, -718), Point(940, 843), Point(9, 749), Point(229, 353), Point(912, -526), Point(-420, 492), Point(-115, -274), Point(384, 429), Point(334, 311), Point(727, 270), Point(253, -625), Point(805, 553), Point(558, 799), Point(727, -483), Point(192, 872), Point(213, -615), Point(796, 115), Point(930, -98), Point(-535, 895), Point(-10, 931), Point(-608, 292), Point(467, 666), Point(378, -463), Point(-252, -108), Point(28, -255), Point(707, -45), Point(89, -683), Point(-540, -741), Point(836, -918), Point(735, -424), Point(-306, 471), Point(-358, 543), Point(-422, -216), Point(316, 383), Point(-350, -535), Point(626, 59), Point(842, 466), Point(504, -895), Point(954, 825), Point(448, -763), Point(-889, -782), Point(898, -946), Point(-606, 500), Point(742, -991), Point(179, -134), Point(27, 490), Point(-333, 12), Point(-18, -50), Point(-654, 214), Point(739, -672), Point(152, 484), Point(-205, -60), Point(606, 820), Point(627, 253), Point(-523, -440), Point(223, -916), Point(-86, -958), Point(-355, -114), Point(437, -160), Point(-813, -371), Point(309, -249), Point(54, 118), Point(-71, -301), Point(-313, -642), Point(802, -501), Point(123, -307), Point(-999, 829), Point(-351, -484), Point(-221, 699), Point(-625, -419), Point(823, 979), Point(-834, 588), Point(-265, -737), Point(718, -448), Point(-763, -420), Point(67, 758), Point(-686, 781), Point(-62, -899), Point(589, -427), Point(930, -219), Point(-308, -98), Point(-690, 576), Point(-159, 894), Point(-438, 607), Point(401, 35), Point(-283, 179), Point(-829, -224), Point(625, 664), Point(-11, -367), Point(505, 589), Point(-793, -410), Point(-641, 920), Point(86, -900), Point(-9, -240), Point(381, 503), Point(-329, 993), Point(561, -312), Point(-422, -131), Point(581, 207), Point(859, -61), Point(-820, 840), Point(876, -263), Point(-951, -662), Point(-33, 910), Point(21, -214), Point(-791, 118))
        // val points3 = List(Point(326, 891), Point(-311, -393), Point(286, -196), Point(-366, -361), Point(-345, -957), Point(346, -425), Point(878, -752), Point(-535, 722), Point(-809, -914), Point(-985, 198), Point(-808, -94), Point(397, -915), Point(229, 166), Point(163, 721), Point(150, 390), Point(-431, -141), Point(350, 33), Point(-403, 565), Point(-748, -141), Point(562, 843), Point(-937, 6), Point(-695, -648), Point(-240, -998), Point(-805, 971), Point(333, -927), Point(991, 228), Point(661, -838), Point(-365, 58), Point(942, 616), Point(-912, 292), Point(589, -235), Point(-176, -792), Point(-242, 150), Point(833, 112), Point(-7, 227), Point(546, 614), Point(-280, 491), Point(-902, -737), Point(-386, -679), Point(731, -803), Point(-873, 978), Point(-20, 247), Point(-334, 933), Point(-646, -752), Point(-920, 503), Point(903, -218), Point(113, 630), Point(-259, 948), Point(-89, -889), Point(-452, 273), Point(619, -488), Point(-902, -525), Point(262, -779), Point(-311, -705), Point(-500, 952), Point(-300, 541), Point(-274, 647), Point(809, -298), Point(381, -582), Point(-779, 263), Point(-150, 617), Point(-888, -1), Point(-805, -50), Point(-118, -353), Point(421, -676), Point(29, -766), Point(-547, -951), Point(-382, -521), Point(498, 76), Point(-807, -195), Point(-267, 753), Point(-123, 551), Point(848, -337), Point(-354, -826), Point(-104, 361), Point(-120, -190), Point(-72, -250), Point(620, 637), Point(-921, -345), Point(222, 266), Point(145, 619), Point(-983, -842), Point(-763, -950), Point(-846, 207), Point(730, -309), Point(-21, -968), Point(-958, -12), Point(847, 143), Point(-307, -282), Point(-166, -767), Point(-870, -39), Point(-234, 398), Point(997, 629), Point(-335, 96), Point(520, 483), Point(-643, 913), Point(279, 37), Point(-16, 689), Point(114, 127), Point(-313, -176), Point(-144, -641), Point(647, -561), Point(183, -450), Point(682, 523), Point(503, 949), Point(5, 838), Point(926, 920), Point(529, 140), Point(428, -789), Point(-428, 773), Point(180, 803), Point(-140, 861), Point(-262, 189), Point(429, 630), Point(-412, 499), Point(-15, -443), Point(468, 647), Point(-208, -682), Point(-434, -156), Point(989, -131), Point(791, 792), Point(939, 327), Point(64, -401), Point(-230, 187), Point(604, 948), Point(156, 774), Point(-209, 815), Point(-263, -687), Point(-675, 925), Point(-255, 285), Point(198, -312), Point(-978, -738), Point(-110, 286), Point(-814, -746), Point(418, 485), Point(-875, 358), Point(-523, 945), Point(929, 150), Point(965, 185), Point(-668, 825), Point(518, -424), Point(648, 888), Point(-489, -572), Point(-587, -775), Point(583, 317), Point(702, 119), Point(16, -177), Point(985, -24), Point(-29, 861), Point(440, 943), Point(-740, 460), Point(-127, -72), Point(854, 292), Point(838, 439), Point(-270, -737), Point(-371, 914), Point(-694, 326), Point(-189, 762), Point(39, 275), Point(-846, -409), Point(255, -318), Point(-770, 776), Point(-871, -530), Point(645, -213), Point(546, -711), Point(-50, 798), Point(435, 618), Point(-674, 602), Point(59, -335), Point(380, -425), Point(411, -102), Point(987, -658), Point(430, 508), Point(737, -944), Point(470, -962), Point(-803, 91), Point(-4, 980), Point(180, 679), Point(-818, -800), Point(-21, 872), Point(386, -647), Point(761, -829), Point(404, -801), Point(-561, 927), Point(-276, 112), Point(336, 113), Point(-470, 959), Point(465, 436), Point(-759, 676), Point(222, 652), Point(107, -991), Point(-49, -310), Point(-722, 963), Point(237, 345), Point(-740, -449), Point(427, -940), Point(-223, -121), Point(552, 186), Point(-84, 247), Point(170, 434), Point(682, -194), Point(831, -278), Point(-205, -676), Point(-50, -61), Point(-330, -323), Point(-815, 342), Point(327, 471), Point(-495, 698), Point(225, -695), Point(-202, -235), Point(956, 763), Point(-700, -162), Point(-448, 565), Point(-858, -171), Point(-468, -908), Point(-895, -432), Point(267, 140), Point(329, 215), Point(489, -755), Point(-566, 533), Point(476, -676), Point(244, 7), Point(242, -439), Point(-566, 203), Point(113, -893), Point(222, 530), Point(914, -4), Point(-955, -860), Point(-522, 650), Point(200, 976), Point(-666, -614), Point(-39, -246), Point(118, 209), Point(-585, 306), Point(-427, -726), Point(49, 15), Point(-521, -180), Point(-522, 135), Point(58, -770), Point(-814, 99), Point(962, 118), Point(-130, -259), Point(-213, 229), Point(-95, 345), Point(-279, -15), Point(928, 32), Point(-952, 967), Point(-899, 246), Point(-16, -9), Point(492, 821))
        // val points4 = List(Point(445, 474), Point(-780, -573), Point(248, 61), Point(980, -68), Point(294, -928), Point(760, -613), Point(779, -476), Point(109, 638), Point(-181, 371), Point(-121, 552), Point(-991, -574), Point(-977, 437), Point(704, -37), Point(411, -6), Point(905, 178), Point(400, -406), Point(774, 547), Point(537, 846), Point(589, 538), Point(167, 671), Point(539, -24), Point(-460, -505), Point(630, 369), Point(620, -511), Point(-707, 907), Point(-359, -325), Point(-285, 422), Point(-35, 69), Point(922, 73), Point(-206, 167), Point(-459, 440), Point(-394, 477), Point(819, -221), Point(431, -309), Point(563, -346), Point(361, 678), Point(-623, 638), Point(843, 966), Point(-650, 155), Point(596, 319), Point(638, 725), Point(-204, -917), Point(-288, -540), Point(564, 40), Point(-390, -912), Point(54, -994), Point(116, 170), Point(-98, -361), Point(-159, -445), Point(857, 88), Point(-481, -579), Point(-413, 102), Point(-441, -546), Point(782, 589), Point(67, 348), Point(-34, -636), Point(347, 612), Point(-787, 421), Point(118, -308), Point(673, -857), Point(-996, 650), Point(-713, 986), Point(338, 93), Point(-689, 379), Point(-132, -998), Point(145, 400), Point(270, -222), Point(-768, -709), Point(-880, 259), Point(693, 886), Point(-262, 581), Point(-907, 439), Point(-688, -505), Point(762, 461), Point(-643, -685), Point(479, 203), Point(212, -531), Point(-361, 95), Point(423, -777), Point(-64, -929), Point(-822, -512), Point(-923, -996), Point(825, -471), Point(53, 605), Point(400, 574), Point(-463, -437), Point(-580, 666), Point(-626, -151), Point(488, -804), Point(-984, -347), Point(145, 827), Point(-46, -678), Point(-48, 776), Point(-754, 103), Point(-454, 603), Point(832, 161), Point(-843, -642), Point(372, 900), Point(232, -932), Point(-243, -679), Point(515, -765), Point(789, -435), Point(-328, 150), Point(346, -337), Point(-736, 706), Point(-539, -817), Point(836, -865), Point(256, 199), Point(14, 300), Point(872, -728), Point(699, -975), Point(-967, 165), Point(740, -589), Point(112, -598), Point(195, -263), Point(-30, -941), Point(-633, 660), Point(-753, -833), Point(-127, 209), Point(-996, 168), Point(406, 544), Point(306, -696), Point(646, 279), Point(-134, 537), Point(39, -320), Point(101, 498), Point(-413, 793), Point(-312, -452), Point(666, 29), Point(787, 846), Point(-87, 646), Point(270, 433), Point(320, -878), Point(-659, -562), Point(200, 816), Point(872, 262), Point(-147, 526), Point(-751, 334), Point(-225, -559), Point(585, -364), Point(-630, 841), Point(887, -252), Point(-479, -375), Point(272, 914), Point(706, 432), Point(-253, 488), Point(-709, 973), Point(-653, -493), Point(-169, 497), Point(420, 614), Point(479, 690), Point(-752, 163), Point(290, 961), Point(168, -970), Point(-920, 914), Point(834, -436), Point(-150, 971), Point(565, -919), Point(-826, 216), Point(-28, 292), Point(154, 170), Point(792, -657), Point(-472, 315), Point(973, -638), Point(-297, -225), Point(-110, -554), Point(-517, -817), Point(-371, 308), Point(311, 484), Point(528, -30), Point(-87, 726), Point(96, 465), Point(-445, -655), Point(-588, 231), Point(54, -403), Point(-985, 263), Point(-9, 631), Point(27, -960), Point(121, -291), Point(598, 972), Point(865, 698), Point(75, -686), Point(447, 719), Point(-954, 331), Point(-438, -515), Point(-55, 582), Point(458, 475), Point(-929, 502), Point(-51, 86), Point(361, 199), Point(155, 195), Point(-380, 512), Point(-266, 806), Point(194, 526), Point(232, -576), Point(878, -104), Point(-480, 15), Point(987, -350), Point(554, 565), Point(182, -984), Point(-665, 638), Point(63, 806), Point(-310, -855), Point(-212, -266), Point(-117, 927), Point(-608, -269), Point(988, 213), Point(-466, 450), Point(536, 145), Point(518, 183), Point(142, -384), Point(808, -495), Point(785, -81), Point(-598, -34), Point(-634, -7), Point(-806, 503), Point(-424, -178), Point(704, 189), Point(682, 229), Point(934, -775), Point(671, -288), Point(-667, 383), Point(653, -887), Point(590, 360), Point(500, 737), Point(-200, -993), Point(550, 994), Point(-272, -619), Point(323, -975), Point(-854, -925), Point(345, 432), Point(882, -375), Point(-366, 782), Point(674, -498), Point(-681, -803), Point(-325, -848), Point(-674, 341), Point(-136, 943), Point(928, 882), Point(633, 635), Point(-280, 444), Point(-171, -614), Point(880, -735), Point(545, -690), Point(672, -669), Point(-57, 593), Point(-963, -666), Point(196, 206), Point(-72, 352), Point(167, 376), Point(547, 449), Point(84, -280), Point(3, -301), Point(-631, -504), Point(134, -718), Point(218, 238), Point(-178, 352), Point(977, 279), Point(-334, -968), Point(-832, 463), Point(565, 817), Point(118, 985), Point(-191, 954), Point(-66, -914), Point(-514, 416), Point(474, 953), Point(886, 221), Point(-390, 446), Point(-302, -966), Point(-744, 393), Point(705, -584), Point(-704, 390), Point(-986, -574), Point(-960, -739), Point(676, -149), Point(101, -484), Point(-171, -514), Point(-352, -475), Point(96, -379), Point(521, 947), Point(-531, 472), Point(-717, 316), Point(241, -118), Point(307, 417), Point(-938, -801), Point(-98, -920), Point(-889, -381), Point(-67, -879), Point(376, -155), Point(715, -67), Point(914, -485), Point(423, -976), Point(704, 608), Point(-691, -901), Point(-134, 209), Point(546, -605), Point(-879, 869), Point(-633, -273), Point(-205, 831), Point(-901, 67))
        // val points5 = List(Point(783, 782), Point(-853, -860), Point(-156, -856), Point(-718, 80), Point(50, 246), Point(-849, 932), Point(192, 351), Point(787, -183), Point(30, -979), Point(10, 128), Point(956, -893), Point(-168, 866), Point(-893, -306), Point(786, -826), Point(-5, -378), Point(943, 397), Point(900, -40), Point(-479, -111), Point(-548, -318), Point(-526, -646), Point(-62, -766), Point(-125, -321), Point(25, -104), Point(-52, 292), Point(-979, 875), Point(351, 463), Point(-494, -962), Point(-503, -762), Point(-207, 145), Point(337, -714), Point(32, 376), Point(211, 269), Point(-628, -266), Point(955, -293), Point(470, -683), Point(-896, 241), Point(-666, -439), Point(-430, 141), Point(161, -292), Point(370, 18), Point(-392, 386), Point(-440, -1), Point(-173, -627), Point(-969, -900), Point(-132, -92), Point(-582, -264), Point(480, 296), Point(89, -399), Point(-502, -646), Point(-969, 564), Point(-291, -804), Point(322, -642), Point(222, 752), Point(916, 364), Point(-27, 746), Point(394, 850), Point(744, -772), Point(300, 565), Point(295, -838), Point(897, 187), Point(436, -877), Point(759, 272), Point(374, 285), Point(244, 942), Point(110, -896), Point(-745, 926), Point(-4, -741), Point(699, -272), Point(-789, 55), Point(-899, -590), Point(118, 872), Point(369, -158), Point(-833, -281), Point(-560, -371), Point(100, -873), Point(378, 851), Point(127, -132), Point(931, 936), Point(-504, -816), Point(658, -52), Point(921, 322), Point(952, 433), Point(500, -204), Point(-682, -494), Point(-262, -662), Point(-286, -431), Point(304, -397), Point(701, -862), Point(378, 847), Point(-660, 147), Point(522, -178), Point(679, 931), Point(571, -399), Point(377, 592), Point(-403, 728), Point(-360, -561), Point(-319, 20), Point(709, -455), Point(135, -800), Point(-246, 394), Point(-933, 369), Point(554, -884), Point(987, 205), Point(588, -694), Point(863, 149), Point(636, 988), Point(802, -284), Point(78, -148), Point(-426, 148), Point(-582, 313), Point(-492, -629), Point(777, -457), Point(-699, 918), Point(-506, -450), Point(-977, 463), Point(-747, -132), Point(-590, -117), Point(-932, -292), Point(755, 700), Point(568, 886), Point(579, 764), Point(-952, 850), Point(-4, -298), Point(588, -59), Point(-362, -58), Point(141, -510), Point(159, -979), Point(-750, 676), Point(509, -499), Point(68, 15), Point(866, -163), Point(-988, 948), Point(537, -601), Point(179, 343), Point(590, -705), Point(-903, 253), Point(-6, -138), Point(638, -887), Point(-711, -995), Point(185, 385), Point(-923, 617), Point(579, -43), Point(-29, 195), Point(-116, 267), Point(-990, 130), Point(121, -551), Point(-837, 413), Point(168, -108), Point(-951, 23), Point(-578, 290), Point(218, -827), Point(548, -53), Point(732, -504), Point(-537, -156), Point(454, -739), Point(-903, 281), Point(-103, -51), Point(-915, 120), Point(-375, 970), Point(-644, -789), Point(594, -272), Point(-112, -978), Point(728, 877), Point(299, -428), Point(-900, -846), Point(927, -566), Point(868, 731), Point(-37, 689), Point(44, 804), Point(389, 276), Point(225, 105), Point(913, -240), Point(575, 473), Point(-787, -484), Point(317, 666), Point(625, -421), Point(679, 46), Point(-280, -295), Point(-977, 224), Point(-859, 637), Point(-184, 417), Point(-396, -810), Point(-34, 931), Point(-723, 428), Point(-383, 453), Point(437, 295), Point(793, -526), Point(117, 725), Point(907, -767), Point(-463, -318), Point(-891, 127), Point(-737, -118), Point(-754, 866), Point(127, 532), Point(-411, 255), Point(846, -368), Point(52, 962), Point(-332, 612), Point(350, 617), Point(736, 843), Point(-143, 732), Point(412, -476), Point(10, 644), Point(-167, -979), Point(976, -231), Point(699, 831), Point(-267, -333), Point(271, 17), Point(609, -721), Point(41, 358), Point(-780, 653), Point(47, -722), Point(428, -113), Point(279, 524), Point(-134, 7), Point(123, 842), Point(-856, -314), Point(-869, -289), Point(312, 935), Point(573, -488), Point(202, -673), Point(-152, 635), Point(122, -884), Point(718, 494), Point(-304, -663), Point(718, -844), Point(-147, 801), Point(238, -273), Point(228, -249), Point(328, 337), Point(-720, -404), Point(561, -1), Point(211, 547), Point(330, 916), Point(-393, -996), Point(-104, 124), Point(655, 366), Point(486, -774), Point(708, -409), Point(-395, 803), Point(923, 53), Point(84, -63), Point(-760, 337), Point(-432, 444), Point(-157, -198), Point(-494, -647), Point(270, -585), Point(78, 880), Point(-298, 444), Point(19, 527), Point(-32, -824), Point(-282, -48), Point(370, -796), Point(158, -418), Point(-296, -907), Point(443, 817), Point(39, 708), Point(-845, -375), Point(923, -531), Point(445, -178), Point(640, 458), Point(-997, -115), Point(481, 109), Point(605, -303), Point(902, -619), Point(975, -816), Point(994, 940), Point(-501, -692), Point(207, -50), Point(807, 765), Point(-60, 406), Point(-761, -778), Point(-90, -758), Point(-186, 803), Point(450, -423), Point(-835, 875), Point(464, 102), Point(-714, -926), Point(-864, -323), Point(-899, 984), Point(-71, -405), Point(-567, -416), Point(-423, -314), Point(-786, -382), Point(-197, 383), Point(-437, -613), Point(737, 338), Point(644, -936), Point(221, 123), Point(501, 2), Point(-326, -257), Point(-339, 118), Point(703, -845), Point(76, 922), Point(-767, -981), Point(-639, -889), Point(425, 242), Point(-66, -359), Point(293, -961), Point(171, 156), Point(314, 318), Point(-322, 264), Point(507, 574), Point(-340, 514), Point(88, 747), Point(-607, -369), Point(-691, 238), Point(-990, 146), Point(739, 183), Point(-486, 364), Point(-281, 550), Point(-471, 553), Point(-416, -94), Point(-929, 101), Point(-103, -941), Point(326, -605), Point(313, 871), Point(102, -408), Point(-498, -195), Point(695, -654), Point(536, 669), Point(842, -550), Point(-77, 311), Point(960, -717), Point(-512, 937), Point(-986, 197), Point(902, 152), Point(350, 25), Point(-385, 771), Point(-217, 472), Point(-288, 413), Point(516, -443), Point(894, -819), Point(855, 186), Point(644, 206), Point(-480, 464), Point(565, -402), Point(-238, -578), Point(-846, -824), Point(988, -133), Point(639, -846), Point(436, 762), Point(-455, -478), Point(-907, 361), Point(624, -636), Point(625, -252), Point(63, -840), Point(92, -939), Point(212, -550), Point(15, 30), Point(-998, -845), Point(-882, -232), Point(457, -339), Point(-721, 763), Point(943, 553), Point(671, -224), Point(-19, 677), Point(502, -69), Point(-387, -950), Point(657, 573), Point(-452, 884), Point(624, 86), Point(192, -365), Point(361, -411), Point(-954, -59), Point(343, -542), Point(-600, -261), Point(-137, -610), Point(-581, -45), Point(840, 316), Point(-73, -327), Point(-585, 441), Point(8, -433), Point(-656, 962), Point(102, 17), Point(507, -553), Point(403, -698), Point(-159, -924), Point(437, 949), Point(606, -832), Point(281, 561), Point(963, -34), Point(774, -965), Point(-777, -439), Point(-561, 667), Point(49, -191), Point(-872, -278), Point(-131, 480), Point(23, -393), Point(-851, -7), Point(934, -544), Point(268, -924), Point(-981, 116), Point(-473, 181), Point(109, 884), Point(676, -924), Point(511, -692), Point(-660, 419), Point(-654, -409), Point(399, -39), Point(-885, -235), Point(-868, -384), Point(418, -280), Point(56, 383), Point(-823, 510), Point(-286, -31), Point(373, -126), Point(599, 909), Point(-165, 817), Point(-971, -185), Point(-470, 508), Point(985, 454), Point(629, -174), Point(925, 210), Point(-818, 628), Point(922, 579), Point(-155, -187), Point(655, 800), Point(-437, 10), Point(-175, 274), Point(426, 242), Point(531, 61), Point(88, 719), Point(509, 294), Point(845, -990), Point(-131, 682), Point(766, -602), Point(163, -784), Point(-620, -424), Point(-377, -814), Point(-923, 858), Point(931, 66), Point(479, 228), Point(-388, 924), Point(334, -3), Point(-266, 446), Point(250, -985), Point(237, 420), Point(-398, 583), Point(-38, -454), Point(875, 747), Point(594, 264), Point(-647, 233), Point(-793, 440), Point(187, 795), Point(-351, 976), Point(896, -667), Point(629, 773), Point(-10, -94), Point(-340, -592), Point(364, 896), Point(384, -34), Point(-301, 898), Point(-344, -908), Point(-351, -105), Point(10, 369), Point(-836, 482), Point(242, -413), Point(-255, 977), Point(-477, -451), Point(117, -741), Point(-312, 869), Point(-639, 331), Point(-533, -917), Point(379, 789), Point(-860, -843), Point(368, -888), Point(544, 936), Point(533, -559), Point(644, 470), Point(-303, 690), Point(995, -312), Point(-61, -496), Point(406, 155), Point(-224, 356), Point(-881, 77), Point(-266, -558), Point(834, -139), Point(-818, -787), Point(-680, -252), Point(245, 275), Point(788, -217), Point(-354, -785), Point(377, -394), Point(-571, 779), Point(305, 852), Point(489, -366), Point(-428, -112), Point(-849, 382), Point(330, -87), Point(-938, -826), Point(-742, 20), Point(708, -105), Point(-900, -962), Point(880, 71), Point(-877, 131), Point(-342, 692), Point(974, -664), Point(-406, -547), Point(943, 658), Point(881, -292), Point(-733, -758), Point(570, -864), Point(-537, 279), Point(465, -918), Point(513, -543), Point(123, -812), Point(217, 718), Point(-799, -259), Point(-530, 298), Point(399, -376), Point(-433, -860), Point(-922, 393), Point(459, -483), Point(-590, -352), Point(335, -490), Point(-265, 593), Point(400, -512), Point(53, 427), Point(-38, 300), Point(-922, -923), Point(408, -435), Point(852, 707), Point(-92, 114), Point(119, -345), Point(483, 309), Point(-96, 129), Point(-618, -638), Point(487, -616), Point(-278, 981), Point(-773, 638), Point(419, -314), Point(-818, 279), Point(528, -356), Point(-506, 2), Point(410, 452), Point(688, -994), Point(-826, -439), Point(886, -232), Point(656, 841), Point(-578, 714), Point(790, 191), Point(75, 848), Point(-456, -462), Point(953, -781), Point(706, 545), Point(352, 948), Point(392, 849), Point(930, 83), Point(437, -686), Point(519, -946), Point(306, -904), Point(374, 892), Point(442, 456), Point(-432, -103), Point(-797, -164), Point(463, -872), Point(-245, -361), Point(805, 128), Point(162, 388), Point(56, -753), Point(-600, -513), Point(-129, 725), Point(-52, -956), Point(104, 86), Point(-859, -95), Point(510, -206), Point(-112, -699), Point(681, -619), Point(685, 879), Point(29, -890), Point(325, 846), Point(-23, 728), Point(231, -292), Point(-464, 86), Point(-926, -415), Point(271, -71), Point(-741, -818), Point(-176, -446), Point(370, -748), Point(367, -5), Point(-963, -664), Point(829, -138), Point(92, 203), Point(-334, 84), Point(934, -952), Point(113, 960), Point(-900, 28), Point(114, 580), Point(548, -367), Point(524, -597), Point(596, 616), Point(206, -11), Point(-186, 948), Point(482, 467), Point(-728, -540), Point(-206, 627), Point(328, -688), Point(304, 217), Point(347, 899), Point(181, -340), Point(-606, 526), Point(579, -854), Point(527, -629), Point(164, 855), Point(-713, 569), Point(-712, -326), Point(14, 376), Point(481, 203), Point(-900, -991), Point(119, 631), Point(419, -412), Point(-304, 104), Point(-785, -432), Point(-17, -633), Point(297, 942), Point(-172, 20), Point(870, 400), Point(608, -268), Point(579, -821), Point(620, 797), Point(680, 900), Point(142, -531), Point(-767, -226), Point(946, 465), Point(-939, -420), Point(251, 595), Point(-633, -790), Point(-682, -458), Point(-856, -57), Point(-510, 305), Point(-40, 814), Point(833, -170), Point(885, 376), Point(777, -280), Point(666, 940), Point(531, -328), Point(-169, 582), Point(-339, -524), Point(-523, -112), Point(-902, 765), Point(-778, 635), Point(361, 973), Point(401, 487), Point(627, 525), Point(652, -593), Point(-325, -101), Point(796, -961), Point(447, 940), Point(695, -910), Point(-454, -739), Point(-793, 209), Point(-840, -702), Point(-884, 356), Point(-68, 945), Point(356, 795), Point(-873, 543), Point(-167, 775), Point(228, 204), Point(-159, -542), Point(566, 852), Point(-74, -556), Point(-618, -194), Point(-389, 997), Point(4, 953), Point(-777, -897), Point(-331, -565), Point(-873, -801), Point(-247, -643), Point(145, 598), Point(715, 514), Point(43, -412), Point(-871, -493), Point(-742, -565), Point(876, 712), Point(-136, 628), Point(541, -39), Point(-461, 397), Point(444, -685), Point(-844, 928), Point(-373, -324), Point(859, 877), Point(419, 572), Point(60, -867), Point(958, 639), Point(-879, -571), Point(110, -931), Point(-909, 419), Point(-151, 821), Point(761, 437), Point(-606, 85), Point(173, 49), Point(897, 633), Point(523, -912), Point(848, -244), Point(-461, -385), Point(664, 119), Point(41, -359), Point(421, -399), Point(-994, 756), Point(-816, -598), Point(-615, 544), Point(645, 721), Point(699, -394), Point(-517, -876), Point(-771, -604), Point(637, -846), Point(-298, -694), Point(-201, 693), Point(186, 606), Point(999, -130), Point(535, -561), Point(361, -542), Point(-845, 698), Point(-128, 446), Point(-760, 603), Point(-580, -742), Point(442, -441), Point(611, -617), Point(495, 760), Point(91, -819), Point(-399, -677), Point(226, -933), Point(-689, 176), Point(-554, -601), Point(761, -937), Point(-602, -599), Point(693, -710), Point(866, -361), Point(461, -315), Point(-412, -562), Point(-837, -382), Point(704, 951), Point(741, -654), Point(-188, -765), Point(286, -360), Point(421, 1000), Point(325, -601), Point(950, -396), Point(-597, -412), Point(800, 113), Point(-796, -452), Point(27, -209), Point(576, -646), Point(-410, -640), Point(-187, 55), Point(-393, -566), Point(267, 173), Point(-859, 76), Point(-73, -142), Point(385, 118), Point(669, 240), Point(-729, -205), Point(397, -328), Point(-411, -444), Point(764, 347), Point(-124, -174), Point(-488, -553), Point(588, 962), Point(-539, 618), Point(223, 29), Point(570, 548), Point(678, 685), Point(-448, 333), Point(-817, -132), Point(513, 540), Point(277, 289), Point(-341, -813), Point(-612, 292), Point(747, 303), Point(-349, -81), Point(142, 915), Point(-175, -716), Point(933, 976), Point(-484, -639), Point(-416, 231), Point(151, 825), Point(358, 650), Point(-573, -271), Point(891, -978), Point(-815, -283), Point(923, -816), Point(-259, 950), Point(333, -884), Point(-809, 235), Point(30, -431), Point(-707, 531), Point(-328, -591), Point(-630, -299), Point(727, 709), Point(486, -275), Point(392, 501), Point(-979, 529), Point(97, 566), Point(872, -73), Point(-50, -918), Point(114, 520), Point(-587, 922), Point(-335, 268), Point(-930, 847), Point(-5, 706), Point(154, 909), Point(98, -341), Point(-934, -117), Point(-436, 230), Point(-599, 551), Point(457, -620), Point(-345, 39), Point(-775, 326), Point(242, 673), Point(-454, 748), Point(221, -514), Point(796, -685), Point(481, 784), Point(-139, 836), Point(-608, -603), Point(-387, 960), Point(-949, -93), Point(-59, -54), Point(-216, 105), Point(84, 979), Point(347, 910), Point(-296, 404), Point(-658, 138), Point(-926, 343), Point(-248, -106), Point(-477, -553), Point(692, -201), Point(-745, 299), Point(834, 86), Point(-48, -529), Point(656, -649), Point(-159, -138), Point(-628, 713), Point(636, 605), Point(-343, -761), Point(-48, 861), Point(-328, -896), Point(-322, -48), Point(360, -910), Point(-596, 909), Point(-519, 489), Point(-721, -611), Point(-921, 960), Point(525, 83), Point(168, 195), Point(981, 352), Point(77, 260), Point(30, 863), Point(95, -686), Point(-954, 514), Point(-331, -364), Point(660, -384), Point(-154, 460), Point(-926, 430), Point(-806, 529), Point(31, -677), Point(672, -740), Point(-648, -511), Point(-22, -792), Point(775, -767), Point(-714, 367), Point(-265, -591), Point(223, -266), Point(-502, 235), Point(921, 85), Point(-614, -568), Point(-916, 764), Point(196, -793), Point(697, 245), Point(746, -612), Point(164, 308), Point(206, 371), Point(-764, 204), Point(-174, -659), Point(-951, 402), Point(-737, -827), Point(372, -67), Point(492, -518), Point(0, -569), Point(605, -921), Point(969, 510), Point(-476, -568), Point(-738, 1), Point(-797, -113), Point(-176, -321), Point(-46, 811), Point(346, -299), Point(-585, 469), Point(-34, 496), Point(450, -556), Point(669, 623), Point(-508, -588), Point(-482, -730), Point(-640, 597), Point(199, 765), Point(-37, -379), Point(254, -993), Point(-452, -177), Point(602, -474), Point(309, 23), Point(291, -950), Point(-72, -682), Point(145, -217), Point(851, 41), Point(122, 637), Point(40, -296), Point(-267, 758), Point(-608, 786), Point(946, -959), Point(142, -419), Point(773, -584), Point(605, -972), Point(736, 131), Point(-333, -178), Point(10, -675), Point(895, 312), Point(49, 713), Point(-949, 249), Point(-810, -817), Point(874, 503), Point(-862, -167), Point(366, -3), Point(-586, -772), Point(-799, -923), Point(734, -233), Point(98, 510), Point(-263, -968), Point(-588, 888), Point(23, -77), Point(-275, 571), Point(-512, 966), Point(-541, -710), Point(897, -365), Point(-906, 762), Point(-476, 759), Point(-407, 169), Point(313, 403), Point(-961, 745), Point(942, -668), Point(-692, -276), Point(468, -943), Point(-757, 470), Point(-701, 431), Point(-544, -801), Point(871, -524), Point(-568, 481), Point(908, 821), Point(-579, 453), Point(570, 793), Point(881, 77), Point(-345, -795), Point(43, 169), Point(-948, 598), Point(-865, 532), Point(673, 868), Point(719, -726), Point(-803, 498), Point(-779, 719), Point(-406, 543), Point(-160, 109), Point(-609, 433), Point(330, 405), Point(808, 901), Point(592, -248), Point(966, 777), Point(694, -129), Point(109, 531), Point(-352, -684), Point(456, -386), Point(-224, -688), Point(-265, -275), Point(-952, 832), Point(-600, 812), Point(-733, 829), Point(-226, -498), Point(549, 816), Point(933, -939), Point(-744, 551), Point(-428, -785), Point(224, -887), Point(-406, 608), Point(-355, 273), Point(-260, 16), Point(914, 220), Point(-389, -946), Point(675, 591), Point(-11, 97), Point(-760, 202), Point(-51, -91), Point(-9, -775), Point(-576, -336), Point(-783, -940), Point(97, 516), Point(280, 590), Point(991, -605), Point(-980, 872), Point(-737, -777), Point(-762, -610), Point(532, -541))

        val n = args(0).toInt

        val fw = new FileWriter("runtimes.log", true)

        for (ti <- 0 to 10) {

            val points6 =  generateSomePoints(n )

            // println(prettyDisplay(findClosestPair(points1)))
            // println(prettyDisplay(findClosestPair(points2)))
            // println(prettyDisplay(findClosestPair(points3)))
            // println(prettyDisplay(findClosestPair(points4)))
            // println(prettyDisplay(findClosestPair(points5)))


            val msBefore = System.currentTimeMillis;
            val closestPair = findClosestPair(points6)
            val msAfter = System.currentTimeMillis;

            // println(prettyDisplay(closestPair))
            // points6.map(p => println( p.printPoint()))
            fw.write(s"Ran for ${n} points in ${msAfter - msBefore} ms\n")



        }
        

        
        fw.close


    }