MZqFpD='
   �        @           JT                        �@� ����H��1ҽ  ��  ��>� p1Ɏ���׉���  ^��r � PP1�� �����   �ٹ �P ��1�1���@t� �1�0��( �H Ou��P%  SR��r,�π�?���������1��ƾ��������������X��[�Z��1��r���PQ�������1۰��YXr�ƃ� ����:v���:6 v0�A�P1��X�ŉ����t	� �����W��$���_�����$������� � ���tQV���$� ^Y��É���tRV1ɱʬ^��Z��BIy��                                                                                                              U�'
#'"
o="$(command -v "$0")"
type ape >/dev/null 2>&1 && exec ape "$o" "$@"
if [ -d /Applications ]; then
dd if="$o" of="$o" bs=8 skip="     398" count="      87" conv=notrunc 2>/dev/null
elif exec 7<> "$o"; then
printf '\177ELF\2\1\1\011\0\0\0\0\0\0\0\0\2\0\076\0\1\0\0\0\373\020\100\000\000\000\000\000\010\012\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0\0\0\0\100\0\070\0\004\000\0\0\000\000\000\000' >&7
exec 7<&-
else
exit 121
fi
exec "$0" "$@"
R=$?

if [ $R -eq 126 ] && [ "$(uname -m)" != x86_64 ]; then
if Q="$(command -v qemu-x86_64)"; then
exec "$Q" "$o" "$@"
else
echo error: need qemu-x86_64 >&2
fi
elif [ $R -eq 127 ]; then
  exec "$o" "$@"
fi
exit $R
error:  
 cpuid oldskool e820 nolong   C�    8 �$                ��   � ��   � ��   �� ��   �� ��   �� ��   �� ��   �OQ�      P   B<  j ��@ ����"�f�Z   �����  � � �i ��z�X�ĀuLf�fXf��f�    f1�fPf�f�fXf9�t9f	�fPf�f�   �f��fG�f9�|f���f�    f!�f9�u1�ÿ�$���$���$�y��Q ��f1�f1�f� �  f�   f�PAMS�r#f9�u��t��r�Eu��f��t�� r�ÿ�$�/��1���H�ؿ �&�P�P&� ��&�=�X�X&�u@� �, ���d�% ���d�% �`P� ���d� X�`�	 ���d� ��d�u���d�t����� y��f� P� f� X� f� @� f� 0� f�  � f� � � f�   1�f�f   ����f� � "���" �f�  "�f��  �2f  0�$ �f  �f���"��!'( j0X�؎Ў�����   E1�E1�E1�E1�1�1�UH��    ޺    �  h  �,$H�l@     ��H�  ���}  H��   �% �     ��  j H��H��)  H�E j j j Ujj hp1@ j UjjY1�1�1�1�1�E1�E1�E1�E1��)	  �w9wuE1��>���G9�t�H�Hk�H�DH�HcWL�H��Hk�H�LHLI9�s�I��   H�L���UI�Ӊ�A�'   SH� ����  L��D��H��%�  L��A��t9A�u@��uE1��)�m���H��t�H��I�I�1��� A��	H��/H!�H��L��[]�AWE1�AVAUATI��UH�oSI��H��RM�qM��tUD���   L��Hk�H�H�PH���H�PH���  HPH�� ���H�� ���H)�tA�yuH�HA��H�PI��뢺   A�   E9�vVI��D�ȉ�J�|���H9|sJ�4�   I��H�~H����u����Hk�H�t�   A��H��H�DH����H�{   �   HCCD�C�C    I�     ���H�HcCI9�sWL�m H�EL�H�$I��    H9$v2K�T= �   L��H���O���H��t� u
L��H��H�I��   ��I��H���X[]A\A]A^A_�@                 @              @       @                    @       @@      `              �1           Q�td    P        ���}   p                                  �
      �
@     �*      0       0                       OpenBSD              NetBSD  @+�5PE  d� kd\        � #            �        @                           2                 �                                    &9  (                                                                                   &9  �                           .text    0      0                 `  p.data    �1 @      @              �  �����           �            H   __PAGEZERO                                                         �   __TEXT            @      @               @                   __text          __TEXT           @      0                                      �   __DATA           @@      �1     @                          __data          __DATA           @@             @                             __bss           __DATA           P@      �1                                        4<W�ʠ4<W�ʠ   �      *             @                                                                                                                    �@                                     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     fD  �AWI��*  AVE1�AUI��ATUSH��H�4$H�T$�e���I���*  ��   A���t=Q�td��   A�G����H�E1�H���H��M9g(vfM9g vH�\$I_L�I9�LB��L���G����   H��H��1��I�WH�4$�   L��L�I��   �h���H� ����  H!�H	�H��I��8�S���M9u M��MCM M�M H��[]A\A]A^A_�1��Ð1���q��SH��tH��� ��0@ M��IE�H�l�1��>  �$H�t$H�T�H�%J�1H���1���@ � @@ ��@@ H)����H�1����H���H�H����>  tj j H�H�@PjH�����  UH�� P@ ��9@ �%�q�%�q�qjX�ǥ1���1���1X�qI�E H�SV���u'I�? u�1�I�<��  u�@I�<� g�Iu��u�H����@ ����"+4=j ��9@ �4j+��9@ �+j+�!:@ �"jc�<:@ �j3�:@ �j?��9@ �j9�	:@ X�0@ H�W�(P@ ���P@ s 1�1�1Ҭ�Ѐ�H��H	Ӏ���u�H�H��ؐ_^[�w=  ��n=  u��=  ��1H��WV�  ^_�@�qj� j�@��=  �P�@~qH�H�@    H��{1���q��=  �P���qH�H�@    H���1���qj�@�i=  �P���qH�H�@    H�Ǜ1��ATA�   US�  1�1�H�=k�1�#  A����A��t D��)�����	Ń�u�H�5��1����  �Ņ�tH�5p�1����  [1�]A\�AUATI��USQH�=Hj1 u!1�1��`"@ H�2j1�}qj�"j1�  H�-j1H�j1H�]�H���tH��H��H�|� u�L�"1��CL�mL;-�i1sH��i1H��L�$�L�-�i1��   �   ��}q��}q�  ��ủ�Z[]A\A]�H�=-z1�F���H�=a�1�:���H�=��1��+���UH��A��I��I��I��������9@ ��9@ H9�tPQ�   �YXH�����   ������u  D��L��L��L���US���qH�CRH�C�5;  j�C�t#jXj��C�C0�CH��  H�C H�C8H�CP�>�t:H�� H�-2+  jXj�Y�C�C0�CHj���H�C j�Y��H�C8j�Y��H�� H�CPX[]Ë�:  �W�1j�XË�:  �G�1j�XË�:  �7�1j�XË�:  �'�1j�XË�:  ��1j�XË�:  ��1j�X��UH��AWAVAUATSH��8�N:  1H�� ��1H	�H���1�Q*  �E�  �4:  �m̸    H�� H��t�и    H��t�к   eH�%`   H�-p�1��  H��ur��	~mH�� ���  � *  ���  �%*  L�-�)  j�YA�պ4@ �.4@ I���*  ���qL����)  H��)  ��  L����j�YA�պ   H����H�� H�o�1�qH�\�1   �U9  t�   eH�%`   ��  
r
H�  ���}  A�   PA�@   H���j�M��@4@ L��  ��j I�� AUH�� ��(  H��8E1�E1�j�H���"   ATAUI��H��1H�� �)  H�җ1L��H�� H�   "   H���A�T��PH�pH���1   ��(  � �  H�� H��  ��H��A�   L���  1�A��Hc�I$���t��\u� /����H�� M��$ �  �m(  I��$ � H�� L��A��  ��  H��I����  H�� L���(  H�� M��L��jXI��$��  I�$D��k@ H��   M��$��  I��$��  1��y  H�H���H������tf�� �f�� �t�f�� �tH��H�VH��V��t- �  ��
�� $  �1��I������  I�PI;PsH�JI�H�H��u��AWH�I��M��AVAUI��ATI��US1�H�� H�<$H��H�t$H�D$�Y����D$�|$ t(�D$��t �� A�ǃ�	��A�tUH���,����D$��1�H���h���M��tH�D$I��L)�L9�IG�A� M���b  I��I9�LG�K�D�     �J  H��L9�s5H�D$H;D$r1�I�D��� @����   �"   H�������I����   �t$����   E��u�� ��   ��	��   ��"t	��\��   1�|$\uH��H���]����D$��E1Ƀ|$"uH���E����D$I����I��M��uH��H���t��\   H���j�����I���P����\   H��I���M�����A���   I�� M�yI9�r�"   H��H���$�����1�L�ȹ   H��H��A������H������H�������D$����1�H��������@���H�� ��[]A\A]A^A_�AVI��AUATE1�UH��SH�Z�fA�; ��   A�D$Hc�L9�sJ�t� Lc�E1�E1�E1�L��I��C�|K�L�ʉ���tnA��fA�� �fA�� �t�f% �f= �uA�S��
L�I�� $��E��u��=t�G���w�� �A��"  L��M�RL9�wI���B�D�H��u�L����L��M�J�tH��M�H��;���[D��]A\A]A^�Hc�Hk�H�1� ��t��t��uHc�H����  Hc�E1�E1�1ɸ    ���j����Hc�Hk�Hʔ1� ��t��t��uHc�H�����  Hc�E1�E1�1ɸ    ���(����ATI��UH��SHc�H��Hk�H��   H�t$�#  Hj�1A��H�KRL��PH�� L�L$<�$  H��0��t�D$�R���Q  ��muA��1��u
��   ��  ��v!H�t$0�ع    H���H��  @ �   1����������k  H�İ   []A\�AWAVUH��SH��H��teH�~ u	H��H����H�^E1�E1�H�H��t2H�s�H�L$�|$����H���t>H�L$IƋ|$H���tH�H;rI��H��L9�u�L���H��1�1�[]A^A_�����H��[]A^A_�H��I��H���t�   1�H���H�V�E1�L���ATI��UH��SHc�H��Hk�H��0H�t$����H �1A��H�KRL��PH�� L�L$<��"  H��0��t�D$���   A��1�A��mt�>  H��0[]A\�AWAV�    AUA��ATI��UH��SH��AQH��t�Є�t�-����yH�{ uH��H��H��u��IH��E1�E1�H�H��t&H�s�L��D���+���H���t=I�I���tI�H;rI��H��L9�u�L���AXL��[D��]1�A\1�A]A^A_�����Z[]A\A]A^A_�eH�%`   ��  �����  �UH��D  H�� �^!  ���U�x1@ ��tH�.��1@ �  ���tz��?t��hu5H�5�1��1@ �  H�5ݏ1H���  H�5Ώ1��1@ �{  1��6H�59o1��1@ �f  H�5(o1H���W  H�5o1��1@ �F  �   �  ]�ATD�%Z^1UH��SE��u]H���  �Ã��u����   E��u8H�=M�1�  ��;uA��Ή���  ��uÍC؃�v��C����t��؃��H��
A��룋��1��t1����1������1� �M  ���t����1@   �z�1����[]A\�UH�5Gn1H��H�=�/  �o  H�51n1��1@ �^  H�5 n1H���O  H�5n1��3@ �>  H�5 n1�=��1��  H�5�m1�
   ]�  �=ܖ1 AVAUI��ATU��SH��u
���1   �=��1 uH���1�8 ��   Hc��1���1    H��I�T� 9�}8H�JH�g�1�:-u(H�JH�W�1�J�a�1��-u"�z ue���R�1H�/�1X�qA����  ��uE�-   H��A���H��1X�q�  H����   ��1-   �H�PH��1� ��1D�%�1L�5ϕ1A��:tD��H���_  H��u!A�> u�ŕ1�=1 t�;:��3@ tu�n�x:tH���1    A�> uu�mA�> t	L�5z�1�S���1���z�19�}H�I�D� H�X�1�1H�C�1X�q�;:A�:   t,�=M�1 t
��3@ �����A�?   �H��1X�q�$�1[D��]A\A]A^�SH��u2H�s[1H�X�H���tLH�r[1H�<�H��uH������������u��-��t�K   ����������G��t;G sH�W� 1�[ú�}qH�H��H���tH�JH��H��H99u�j ���1�� t_USH��Q� uO�W1�#c-  ;e-  t<�SH9�v+H�s�{H)�H��	  H���u�i�1�C����H����C    1�Z[]�ËGH��;GsH�W�p�w��H���   �   H�|$�c  I�����M��t�D$H���AUATUH��SQ�G;GsH�W�H�OD�$�����A�ă��uA����vA���   vmA���w"D��   A�   ��������A)��˃��A�   �   D!�A��t/H���7����ǃ��t�%�   =�   u
����?	���H���  �A��ZD��[]A\A]�H���
t�F;F r,H���   �   @�|$H�|$��  H��t"�D$H��À>t�H�V�p�q@�<@��ø������SH���1�I���L��H��H�Y�H��   H���p  H��u	A���H��uA��D��[�AUATUH��SH��(�A#o+  ;y+  u	H� +  �I���A�q9�vH�+  �x�1�E1��  M���I��I��L��)�H��I9�IF�Hu�I9�s	DM�   uH�E    �   �}���uH��1�H�E    I���E�����   L��I�H)؀} L�$H�D$t*�U H��L9�vH�MH�L$��v
��H�D$�H�T$�H�D$    H�D$    �   H����  H���u���1�"���H�T$H�E    H9�s
)ЉEL���H�1�I��I9�v�E����H��([]A\A]�AUATUSH��H��(�A#*  ;*  uH��)  �4�1�;  I��H��D�A�A I��I��H�yD)�H9���   �9��   I�H��L��L���D�kS�SA�����   �;��   H�k�
   H���2	  H����   H�PH��D��H)��?  H��H���u)Hc��1H;()  H����   H;)  ��   �   H�{�SH�4H)��  )k�|D�SA���u2H9�HF�1�I�L��H��H��L��I��H��H)�H����C����C�@H�<$D��H��D��H�T$�   H�D$L�L$�  H��u��1�CE1���C    H��(L��[]A\A]�ATA����SQtE�FH���tH�V�ȉFD�$�"�V;V s �B�FH�vH�~��  H�CD� E���A���D��Z[A\�U���i.@ H��t1��Љ��%  AWAVI��AUI��ATI��USH��H��H�?��   E1���tM�E I�}  I�,$tH��H��H��1Ҹ   �   H��H��HC�H��H��H��pqH��N�t6I��H��pa�    H��tPH�sL�D$L��H�����I��H��t6L�D$M��uI�u H��tH��H���H)�I�</H���  M�4$�M�} ��`�����i���1�H��[]A\A]A^A_�AUATUH��S�   QD�%�&  H��A��t�]���=�	  �   HN�1�H9�|?I�   �   ��  H��E��t�+����   =�	  �  �/LN�HN�L�1�H9���Z��[]A\A]�H��H��H��H��L��L��H1��Ѕ�xj��xfL�Ն1Hc�L9�s"Hk�Hʆ1�9uH�yHc�H����    ���&  ��u��  L9�r�*���À�tHk�H=��1�p  �����*���Å���   H��L�]�1Hc�L9�s2Hk�HR�1�9u"H�4$H�yH��H���H�T$�   �    ���[�}%  ��u�[  �IL9�r�����=��H�4$H�T$tHk��   H��H=�1�   ��   H������������H��Ã?u�   �M����E1�E1�Lc�M9�v:1�J�H9Nv"H�WA�Ӄ�� u���H�D�ڊ�H����I��H��I����L���ATA��U��SH���H��D����   H���t"H�SH9�wH����H)�u��H)�HH�S�Hc�1H;�$  u��u�1�[]A\Ë��t
��uI�J   L�WI��1�E1�A9�}8I�JM�BL9�s%I)�I�II�9I�2I9�LG�A��I��L��L������J����1���9�~H��I��I��J�|� t�����Lc���u1��H�W�у��u�����I��J���   Å�xj��xfL�S�1Hc�L9�s"Hk�HH�1�9uH�yHc�H����    ����#  ��u�q  L9�r����À�tHk�H=�1�6������������ø   ��)   w%��'   w1�� t,w��	���	��    ��
�����_   t�� 0  �����fnΉ�W�H���f`�(��fa�fp� ft�(�ft�W�V�f�������u(OH��(�ft�ft�V�f������H��H�H�@��t�8 u1�É�1���v �ϋMJ4@ ������?��H����u��H	��H��1�H��w*H��v	H�H�D7��H��v��D7��H��tH�Ɉu��1���AUI��ATI��UH��SQH�P�1H��uH�@�1H�q�H�q�;�u2�    H��t!�  �   ��H��tH�XH��H��1��7����%�����������Hk��H�1�L�cH�kL�k Z[]A\A]�ATUH��S�   H�=ą1H��tg���t9�ډ��������!�H��tHk�H9l7 u�Hk�!H�H�QH��t�H�y���H��L�guM��t�    H��t��L�%_�1�L���[]A\�H��I��H��H��wMH��vH�6I�T�H�7H�T��H��v�6A�T��7�T��H��vf�6fA�T�f�7f�T��H��t���H9�w��H�R�H�<H�4����AUATU��SP�`"@ H��t1���D�- �1E��t4H�� H��  L�%�  j�YA��D��H����j�YA�Ժ   H����H�� ��9@ H���9@ vH�������   f.�     H���x��%    H�@ B @ �%   H���y��%    1�H��H��r@8t�H��u�H�Ð��   ��  t,H��(��  H�� �Ǹ    H��u����ЉC�1H���ZÉ7�1H���Ë�  U����t�P���u�u�pu$�u.j�^��   ����1j�^�  ���ކ1jXj�^���І1@��H�� ���8  �,   ��j�Yj j �$H�� ��r�H���%�  =�  tI��UH���H=���s��؉��1j�XË*  ��H��(�H��4�H����%�  f=�t�I��UH���u�:�1�A��A��   ����D	��Ӑf�METAL=1 asc2bin ?h Usage:   [-?h] [FILE...] <binary.txt >binary.bin
Converts ASCII binary to ACTUAL binary, e.g.

    $ { printf 'λx.x' | o/lam2bin | o/asc2bin; printf abc; } | o/Blc
    abc

    $ printf '
    (00 (01 (01 10 ((01 (00 (01 10 10))
                        (00000000 (01 (01 110 ((01 11110 11110)))
                                      (00 (01 (01 10 11110) 110)))))))
            (0000 10)))
    ' | asc2bin | xxd -b
    00000000: 00010110 01000110 10000000 00010111 00111110 11110000  .F..>.
    00000006: 10110111 10110000 01000000                             ..@

FLAGS

  -h      Help
  -?      Help
  --  illegal option option requires an argument x t e r m - t r u e c o l o r   T E R M   �                           �������������������������  kernel32.dll 
Cosmopolitan
Copyright 2020 Justine Alexandra Roberts Tunney

Permission to use, copy, modify, and/or distribute this software for
any purpose with or without fee is hereby granted, provided that the
above copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL
WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE
AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL
DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE. 
getopt (BSD-3)
Copyright 1987, 1993, 1994 The Regents of the University of California  �      CreateFileMappingNumaW    ExitProcess   FreeEnvironmentStringsW   GetCommandLineW   GetConsoleMode    GetCurrentProcessId   GetEnvironmentStringsW    GetLastError    GetStdHandle    MapViewOfFileExNuma   ReadFile    SetConsoleCP    SetConsoleMode    SetConsoleOutputCP    SetEnvironmentVariableW   WriteFile P9          �4   @                      f��7      
8      8      28      D8      V8      l8      �8      �8      �8      �8      �8      �8      �8       9      9              D@     P@     \@     �#	NT  	&K ' #	NT  #	NW  �N�NW m���������
����#	NT ��� f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     f.�     ��7      
8      8      28      D8      V8      l8      �8      �8      �8      �8      �8      �8      �8       9      9                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      