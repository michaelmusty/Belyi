s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T34-[4,4,3]-44-44-3311-g1";
s`BelyiDBFilename := "8T34-[4,4,3]-44-44-3311-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 4, 5, 6, 7, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 5, 7, 6, 8, 1, 3, 2, 4 ]:
 Order := 96 > |
[ 4, 6, 7, 8, 1, 3, 2, 5 ],
[ 6, 5, 7, 1, 3, 8, 2, 4 ],
[ 2, 3, 1, 4, 6, 7, 5, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 6, 7, 8, 1, 3, 2, 5 ],
\[ 6, 5, 7, 1, 3, 8, 2, 4 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 96 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 6, 7, 8, 1, 3, 2, 5 ],
\[ 6, 5, 7, 1, 3, 8, 2, 4 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 96 >) |
[ PermutationGroup<8 |  
\[ 4, 6, 7, 8, 1, 3, 2, 5 ],
\[ 6, 5, 7, 1, 3, 8, 2, 4 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 96 > |
[ 4, 6, 7, 8, 1, 3, 2, 5 ],
[ 4, 5, 6, 2, 1, 8, 3, 7 ],
[ 2, 8, 3, 5, 6, 4, 7, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 4, 5, 6, 7, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 5, 7, 6, 8, 1, 3, 2, 4 ]:
 Order := 96 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 4, 5, 6, 7, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 5, 7, 6, 8, 1, 3, 2, 4 ]:
 Order := 96 > |
[ 4, 6, 7, 8, 1, 3, 2, 5 ],
[ 6, 5, 7, 1, 3, 8, 2, 4 ],
[ 2, 3, 1, 4, 6, 7, 5, 8 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 4, 5, 6, 7, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 5, 7, 6, 8, 1, 3, 2, 4 ]:
 Order := 96 > |
[ 5, 6, 4, 8, 2, 1, 3, 7 ],
[ 7, 6, 5, 3, 8, 1, 2, 4 ],
[ 2, 3, 1, 4, 6, 7, 5, 8 ]
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
