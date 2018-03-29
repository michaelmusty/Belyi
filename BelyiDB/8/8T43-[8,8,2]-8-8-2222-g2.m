s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T43-[8,8,2]-8-8-2222-g2";
s`BelyiDBFilename := "8T43-[8,8,2]-8-8-2222-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 4, 8, 7, 2, 5, 1, 6 ],
[ 8, 1, 5, 6, 2, 7, 3, 4 ],
[ 6, 3, 2, 5, 4, 1, 8, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 8, 1, 5, 6, 2, 7, 3, 4 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 8, 1, 5, 6, 2, 7, 3, 4 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 8, 1, 5, 6, 2, 7, 3, 4 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 4, 8, 7, 2, 5, 1, 6 ],
[ 6, 8, 2, 1, 7, 5, 3, 4 ],
[ 5, 6, 4, 3, 1, 2, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 8, 1, 5, 6, 2, 7, 3, 4 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 6, 1, 5, 3, 7, 4, 8, 2 ],
[ 5, 1, 7, 3, 6, 8, 2, 4 ],
[ 7, 6, 8, 5, 4, 2, 1, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 4, 8, 7, 2, 5, 1, 6 ],
[ 8, 1, 5, 6, 2, 7, 3, 4 ],
[ 6, 3, 2, 5, 4, 1, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 1, 7, 2, 8, 4, 5, 6 ],
[ 8, 1, 4, 7, 6, 2, 5, 3 ],
[ 6, 3, 2, 5, 4, 1, 8, 7 ]
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
