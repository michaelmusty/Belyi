s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[5,15,3]-51111-531-333-g0";
s`BelyiDBFilename := "9T33-[5,15,3]-51111-531-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 5, 15, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 9, 8, 5, 4, 6, 3, 1, 7, 2 ],
[ 3, 7, 9, 6, 4, 5, 8, 2, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
\[ 9, 8, 5, 4, 6, 3, 1, 7, 2 ],
\[ 3, 7, 9, 6, 4, 5, 8, 2, 1 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
\[ 9, 8, 5, 4, 6, 3, 1, 7, 2 ],
\[ 3, 7, 9, 6, 4, 5, 8, 2, 1 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
\[ 9, 8, 5, 4, 6, 3, 1, 7, 2 ],
\[ 3, 7, 9, 6, 4, 5, 8, 2, 1 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 9, 8, 5, 4, 6, 3, 1, 7, 2 ],
[ 3, 7, 9, 6, 4, 5, 8, 2, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 9, 8, 5, 4, 6, 3, 1, 7, 2 ],
[ 3, 7, 9, 6, 4, 5, 8, 2, 1 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
