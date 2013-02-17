(** 


The original statement on http://de3.aminet.net/dev/lang/brainfuck-2.readme

<< 
Short:        240 byte compiler. Fun, with src. OS 2.0
Uploader:     umueller amiga physik unizh ch
Type:         dev/lang
Architecture: m68k-amigaos

The brainfuck compiler knows the following instructions:

Cmd  Effect                               
---  ------                               
+    Increases element under pointer      
-    Decrases element under pointer       
>    Increases pointer                    
<    Decreases pointer                    
[    Starts loop, flag under pointer      
]    Indicates end of loop                
.    Outputs ASCII code under pointer     
,    Reads char and stores ASCII under ptr

Who can program anything useful with it? :)
>>

*)

Inductive command :=
| Inc: command
| Dec: command
| Left: command
| Right: command
| Input: command
| Output: command
| Loop: list command -> command
.
